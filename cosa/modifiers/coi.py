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

from cosa.utils.formula_mngm import get_free_variables
from cosa.printers.factory import HTSPrintersFactory

class ConeOfInfluence(object):

    var_deps = None
    fv_dict = None
    
    def __init__(self):
        self.var_deps = {}
        self.fv_dict = {}

    def _intersect(self, set1, set2):
        for el in set2:
            if el in set1:
                return True

        return False

    def _free_variables(formula):
        if formula not in fv_dic:
            fv = get_free_variables(formula)
            fv_dic[formula] = set([TS.get_ref_var(v) for v in fv])
            #fv_dic[formula] = get_func_free_variables(formula, TS.get_ref_var)

        return fv_dic[formula]


    def _build_var_deps(self, hts):

        if self.var_deps != {}:
            return
        
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
        
    
    def coi(self, hts, prop):

        self._build_var_deps(hts)
         
        coi_vars = self._free_variables(prop)

        if hts.assumptions is not None:
            for assumption in hts.assumptions:
                for v in self._free_variables(assumption):
                    coi_vars.add(v)

        if hts.lemmas is not None:
            for lemma in hts.lemmas:
                for v in self._free_variables(lemma):
                    coi_vars.add(v)
                    
        coits = TS("COI")

        visited = []
        while True:
            added = False
            for v in coi_vars:
                if v in visited:
                    continue
                
                for dv in self.var_deps[v]:
                    coi_vars.add(dv)
                added = True
                visited.append(v)
                break

            if not added:
                break

        trans = list(conjunctive_partition(hts.single_trans(include_ftrans=True)))
        invar = list(conjunctive_partition(hts.single_invar(include_ftrans=True)))

        coits.trans = [f for f in trans if self._intersect(coi_vars, self._free_variables(f))]
        coits.invar = [f for f in invar if self._intersect(coi_vars, self._free_variables(f))]
        coits.init = [f for f in init if self._intersect(coi_vars, self._free_variables(f))]

        Logger.log("COI reduction", 0)
        Logger.log(" - Vars %s -> %s"%(len(hts.vars), len(coi_vars)), 0)
        Logger.log(" - Init %s -> %s"%(len(init), len(coits.init)), 0)
        Logger.log(" - Invar %s -> %s"%(len(invar), len(coits.invar)), 0)
        Logger.log(" - Trans %s -> %s"%(len(trans), len(coits.trans)), 0)

        coits.trans = And(coits.trans)
        coits.invar = And(coits.invar)
        coits.init = And(coits.init)

        coits.vars = hts.vars
        coits.input_vars = hts.input_vars
        coits.output_vars = hts.output_vars
        coits.state_vars = hts.state_vars

        new_hts = HTS("COI")
        new_hts.add_ts(coits)

        # printer = HTSPrintersFactory.printer_by_name("STS")
        # with open("/tmp/coi_model.ssts", "w") as f:
        #     f.write(printer.print_hts(new_hts, []))


        return new_hts
        
