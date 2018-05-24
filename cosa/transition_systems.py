# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Symbol, And, TRUE, simplify
from cosa.utils.formula_mngm import get_free_variables, substitute

NEXT = "_N"
PREV = "_P"
AT = "_AT"
ATP = "_ATP"

L_ABV = "QF_ABV"
L_BV = "QF_BV"

class HTS(object):

    tss = None
    sub = None
    name = None
    inputs = None
    outputs = None
    state_vars = None
    assumptions = None
    lemmas = None

    init = None
    trans = None
    invar = None

    logic = None
    en_simplify = False
    
    def __init__(self, name):
        self.tss = []
        self.sub = []
        self.vars = set([])
        self.state_vars = set([])
        self.name = name
        self.inputs = set([])
        self.outputs = set([])
        self.assumptions = None
        self.lemmas = None

        self.init = None
        self.trans = None
        self.invar = None

        self.logic = L_BV
        self.en_simplify = False
        
    def add_sub(self, sub):
        self.sub.append(sub)

    def add_var(self, var):
        self.vars.add(var)

    def add_state_var(self, var):
        self.state_vars.add(var)

    def update_logic(self, logic):
        if (self.logic == L_BV) and (logic == L_ABV):
            self.logic = L_ABV
        
    def add_ts(self, ts):
        if self.en_simplify:
            ts.init = simplify(ts.init)
            ts.invar = simplify(ts.invar)
            ts.trans = simplify(ts.trans)
        
        self.tss.append(ts)
        for v in ts.vars:
            self.vars.add(v)
        for v in ts.state_vars:
            self.state_vars.add(v)
            
        self.update_logic(ts.logic)

    def add_assumption(self, assumption):
        if self.assumptions is None:
            self.assumptions = []

        self.assumptions.append(assumption)

    def add_lemma(self, lemma):
        if self.lemmas is None:
            self.lemmas = []

        self.lemmas.append(lemma)
        
    def is_input(self, var):
        return var in self.inputs
        
    def remove_invars(self):
        for ts in self.tss:
            ts.remove_invar()

    def single_init(self):
        if self.init is None:
            self.init = TRUE()
            for ts in self.tss:
                if ts.init is not None:
                    self.init = And(self.init, ts.init)

        return self.init

    def single_trans(self):
        if self.trans is None:
            self.trans = TRUE()
            for ts in self.tss:
                if ts.trans is not None:
                    self.trans = And(self.trans, ts.trans)

        return self.trans

    def single_invar(self, rebuild=False):
        if (self.invar is None) or (rebuild):
            self.invar = TRUE()
            for ts in self.tss:
                if ts.invar is not None:
                    self.invar = And(self.invar, ts.invar)

        if self.assumptions is not None:
            return And(self.invar, And(self.assumptions))

        return self.invar

    def reset_formulae(self):
        self.init = None
        self.invar = None
        self.trans = None
    
    def combine(self, other_hts):
        for ts in other_hts.tss:
            self.add_ts(ts)

        for v in other_hts.state_vars:
            self.state_vars.add(v)
            
        for v in other_hts.inputs:
            self.inputs.add(v)

        for v in other_hts.outputs:
            self.outputs.add(v)

        for v in other_hts.vars:
            self.vars.add(v)

        if other_hts.assumptions is not None:
            for assumption in other_hts.assumptions:
                self.add_assumption(assumption)

        if other_hts.lemmas is not None:
            for lemma in other_hts.lemmas:
                self.add_lemma(lemma)
            
    def __copy__(self):
        cls = self.__class__
        new_hts = cls.__new__(cls)
        new_hts.__dict__.update(self.__dict__)
        new_hts.tss = list(new_hts.tss)
        new_hts.sub = list(new_hts.sub)
        return new_hts

    def print_statistics(self, name=None):
        stat = []
        stat.append("Statistics (%s):"%(self.name if name is None else name))
        stat.append("  Variables:\t%s"%(len(self.vars)))
        stat.append("  StateVars:\t%s"%(len(self.state_vars)))
        stat.append("  Inputs:\t%s"%(len(self.inputs)))
        stat.append("  Outputs:\t%s"%(len(self.outputs)))
        return "\n".join(stat)
    
class TS(object):

    vars = None
    state_vars = None
    init = None
    trans = None
    invar = None
    
    comment = None
    logic = None

    def __init__(self, vars, init, trans, invar):
        self.vars = vars
        self.state_vars = set([])
        self.init = init
        self.trans = trans
        self.invar = invar

        self.comment = ""
        self.logic = L_BV

    def __repr__(self):
        return "V: %s\nSV: %s\nI: %s\nT: %s\nC: %s"%(str(self.vars), str(self.state_vars), str(self.init), str(self.trans), str(self.invar))
        
    def remove_invar(self):
        if self.invar is not None:
            self.trans = And([self.trans, self.invar, TS.to_next(self.invar)])
            self.init = And(self.init, self.invar)

        self.invar = None

    @staticmethod
    def is_prime(v):
        return v.symbol_name()[-len(NEXT):] == NEXT

    @staticmethod
    def is_prev(v):
        return v.symbol_name()[-len(PREV):] == PREV

    @staticmethod
    def get_ref_var(v):
        if TS.is_prime(v):
            return Symbol(v.symbol_name()[:-len(NEXT)], v.symbol_type())
        if TS.is_prev(v):
            return Symbol(v.symbol_name()[:-len(PREV)], v.symbol_type())
        return v
        
    @staticmethod
    def get_prime(v):
        return Symbol(TS.get_prime_name(v.symbol_name()), v.symbol_type())

    @staticmethod
    def get_prev(v):
        return Symbol(TS.get_prev_name(v.symbol_name()), v.symbol_type())
    
    @staticmethod
    def get_timed(v, t):
        return Symbol(TS.get_timed_name(v.symbol_name(), t), v.symbol_type())

    @staticmethod
    def get_ptimed(v, t):
        return Symbol(TS.get_ptimed_name(v.symbol_name(), t), v.symbol_type())

    @staticmethod
    def get_prefix(v, pref):
        return Symbol(TS.get_prefix_name(v.symbol_name(), pref), v.symbol_type())
    
    @staticmethod
    def get_prime_name(name):
        return ("%s"+NEXT) % name

    @staticmethod
    def get_prev_name(name):
        return ("%s"+PREV) % name
    
    @staticmethod
    def get_timed_name(name, t):
        return "%s%s%s" % (name, AT, str(t if t > 0 else 0))

    @staticmethod
    def get_ptimed_name(name, t):
        return "%s%s%s" % (name, ATP, str(t if t > 0 else 0))

    @staticmethod
    def get_prefix_name(name, pref):
        return "%s%s" % (pref, name)
    
    @staticmethod
    def to_next(formula):
        varmap = []
        for v in get_free_variables(formula):
            vname = v.symbol_name()
            varmap.append((vname,TS.get_prime_name(vname)))
            varmap.append((TS.get_prev_name(vname),vname))
        return substitute(formula, dict(varmap))

    @staticmethod
    def to_prev(formula):
        varmap = []
        for v in get_free_variables(formula):
            vname = v.symbol_name()
            varmap.append((vname,TS.get_prev_name(vname)))
            varmap.append((TS.get_prime_name(vname),vname))
        return substitute(formula, dict(varmap))
    
    @staticmethod
    def has_next(formula):
        varlist = get_free_variables(formula)
        for v in varlist:
            if TS.is_prime(v):
                return True
        return False
    
