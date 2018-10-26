# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.rewritings import conjunctive_partition
from pysmt.shortcuts import And, TRUE

from cosa.representation import TS, HTS
from cosa.utils.formula_mngm import get_free_variables
from cosa.printers.factory import HTSPrintersFactory
from cosa.utils.logger import Logger

class ConeOfInfluence(object):

    var_deps = None
    fv_dict = None
    int_dict = None

    save_model = False
    
    def __init__(self):
        self.fv_dict = {}
        self.int_dict = {}

    def _intersect(self, set1, set2):
        el1 = (set1,set2)
        el2 = (set2,set1)
        if (el1 in self.int_dict) or (el2 in self.int_dict):
            return self.int_dict[el1]

        ret = False
        for el in set1:
            if el in set2:
                ret = True
                break

        self.int_dict[el1] = ret
        return ret

    def _free_variables(self, formula):
        if formula not in self.fv_dict:
            fv = get_free_variables(formula)
            self.fv_dict[formula] = frozenset([TS.get_ref_var(v) for v in fv])

        return self.fv_dict[formula]

    def _build_var_deps(self, hts):

        if self.var_deps is not None:
            return

        self.var_deps = {}
        
        ftrans = hts.single_ftrans()
        for var, cond_assign_list in ftrans.items():
            for refvar in self._free_variables(var):
                if refvar not in self.var_deps:
                    self.var_deps[refvar] = []

                for cass in cond_assign_list:
                    self.var_deps[refvar] += list(self._free_variables(cass[0]))
                    self.var_deps[refvar] += list(self._free_variables(cass[1]))

        trans = list(conjunctive_partition(hts.single_trans(include_ftrans=False)))
        invar = list(conjunctive_partition(hts.single_invar(include_ftrans=False)))
        init = list(conjunctive_partition(hts.single_init()))

        for ts_formula in [invar, trans, init]:
            for f in ts_formula:
                fv = self._free_variables(f)
                for v in fv:
                    if v not in self.var_deps:
                        self.var_deps[v] = []
                    self.var_deps[v] += list(fv)
                    self.var_deps[v] = [x for x in set(self.var_deps[v]) if x != v]

    def compute(self, hts, prop):
        Logger.log("Building COI", 1)

        self._build_var_deps(hts)
         
        coi_vars = set(self._free_variables(prop))

        if (len(coi_vars) < 1) or (self.var_deps == {}):
            return hts

        if hts.assumptions is not None:
            for assumption in hts.assumptions:
                for v in self._free_variables(assumption):
                    coi_vars.add(v)

        if hts.lemmas is not None:
            for lemma in hts.lemmas:
                for v in self._free_variables(lemma):
                    coi_vars.add(v)

        coits = TS("COI")


        coi_vars = list(coi_vars)
        i = 0
        visited = set([])
        while i < len(coi_vars):
            var = coi_vars[i]
            if (var in visited) or (var not in self.var_deps):
                i += 1
                continue
            
            coi_vars = coi_vars[:i+1] + list(self.var_deps[var]) + coi_vars[i+1:]
            
            visited.add(var)
            i += 1
            
        coi_vars = frozenset(coi_vars)
            
        trans = list(conjunctive_partition(hts.single_trans(include_ftrans=True)))
        invar = list(conjunctive_partition(hts.single_invar(include_ftrans=True)))
        init = list(conjunctive_partition(hts.single_init()))
        
        coits.trans = [f for f in trans if self._intersect(coi_vars, self._free_variables(f))]
        coits.invar = [f for f in invar if self._intersect(coi_vars, self._free_variables(f))]
        coits.init = [f for f in init if self._intersect(coi_vars, self._free_variables(f))]

        Logger.log("COI statistics:", 1)
        Logger.log("  Vars:  %s -> %s"%(len(hts.vars), len(coi_vars)), 1)
        Logger.log("  Init:  %s -> %s"%(len(init), len(coits.init)), 1)
        Logger.log("  Invar: %s -> %s"%(len(invar), len(coits.invar)), 1)
        Logger.log("  Trans: %s -> %s"%(len(trans), len(coits.trans)), 1)

        coits.trans = And(coits.trans)
        coits.invar = And(coits.invar)
        coits.init = And(coits.init)

        coits.vars = set([])
        for bf in [init,invar,trans]:
            for f in bf:
                for v in self._free_variables(f):
                    coits.vars.add(v)

        coits.input_vars = set([v for v in coi_vars if v in hts.input_vars])
        coits.output_vars = set([v for v in coi_vars if v in hts.output_vars])
        coits.state_vars = set([v for v in coi_vars if v in hts.state_vars])

        new_hts = HTS("COI")
        new_hts.add_ts(coits)

        if self.save_model:
            printer = HTSPrintersFactory.printer_by_name("STS")
            with open("/tmp/coi_model.ssts", "w") as f:
                f.write(printer.print_hts(new_hts, []))

        return new_hts
        
