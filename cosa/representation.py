# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Symbol, And, Or, TRUE, simplify, EqualsOrIff, get_type, Implies, Not, Ite
from cosa.utils.formula_mngm import get_free_variables, substitute
from cosa.utils.logger import Logger

NEXT = "__N"
PREV = "__P"
AT = "__AT"
ATP = "__ATP"
CPREF = "__"

L_ABV = "QF_ABV"
L_BV = "QF_BV"

FLATTEN = "FLATTEN"
LINKS = FLATTEN+"_LINKS"

apply_prefix = lambda name, prefix: ".".join(name.split(".")[:-1]+[prefix+name.split(".")[-1]]) if prefix not in name else name

class HTS(object):

    tss = None
    subs = None
    name = None
    vars = None
    params = None
    state_vars = None
    input_vars = None
    output_vars = None
    assumptions = None
    lemmas = None

    model_info = None

    _s_init = None
    _s_trans = None
    _s_ftrans_t = None
    _s_ftrans_i = None
    _s_ftrans = None
    _s_invar = None

    logic = None
    en_simplify = False
    is_flatten = False

    def __init__(self, name=""):
        self.tss = set([])
        self.subs = set([])
        self.vars = set([])
        self.params = []
        self.name = name
        self.state_vars = set([])
        self.input_vars = set([])
        self.output_vars = set([])

        self.assumptions = None
        self.lemmas = None

        self._s_init = None
        self._s_trans = None
        self._s_ftrans = None
        self._s_ftrans_t = None
        self._s_ftrans_i = None
        self._s_invar = None

        self.logic = L_BV
        self.en_simplify = False

    def apply_var_prefix(self, prefix):
        remapdic = dict([(v.symbol_name(), apply_prefix(v.symbol_name(), prefix)) for v in self.vars]+\
                        [(TS.get_prime(v).symbol_name(), apply_prefix(TS.get_prime(v).symbol_name(), prefix)) for v in self.vars])

        p_init = None
        p_trans = None
        p_invar = None
        p_assumptions = None
        p_lemmas = None

        if self.assumptions is not None:
            p_assumptions = [substitute(a, remapdic) for a in self.assumptions]
        if self.lemmas is not None:
            p_lemmas = [substitute(l, remapdic) for l in self.lemmas]
        p_params = [Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.params]

        self.vars = set([])
        self.state_vars = set([])
        self.input_vars = set([])
        self.output_vars = set([])
        self.hidden_vars = set([])

        self._s_init = None
        self._s_trans = None
        self._s_ftrans_t = None
        self._s_ftrans_i = None
        self._s_ftrans = None
        self._s_invar = None

        self.assumptions = p_assumptions
        self.lemmas = p_lemmas
        self.params = p_params

        tss = self.tss
        self.tss = set([])
        for ts in tss:
            self.add_ts(ts.apply_var_prefix(prefix), reset=False)

        self.reset_formulae()

    def add_sub(self, name, sub, parameters):
        self.subs.add((name, parameters, sub))

        self.reset_formulae()

    def add_param(self, param):
        self.params.append(param)
        self.vars.add(param)

    def add_input_var(self, var):
        self.input_vars.add(var)
        self.vars.add(var)

    def add_output_var(self, var):
        self.output_vars.add(var)
        self.vars.add(var)

    def add_state_var(self, var):
        self.state_vars.add(var)
        self.vars.add(var)

    def add_var(self, var):
        self.vars.add(var)

    def update_logic(self, logic):
        if (self.logic == L_BV) and (logic == L_ABV):
            self.logic = L_ABV

    def add_ts(self, ts, add_vars=True, reset=True):
        if self.en_simplify:
            ts.init = simplify(ts.init)
            ts.invar = simplify(ts.invar)
            ts.trans = simplify(ts.trans)

        self.tss.add(ts)

        if add_vars:
            for v in ts.vars:
                self.vars.add(v)

                if (v in ts.state_vars) and (v not in self.input_vars):
                    self.state_vars.add(v)

                if v in ts.input_vars:
                    self.input_vars.add(v)

                if (v in ts.output_vars) and (v not in self.input_vars):
                    self.output_vars.add(v)

        self.update_logic(ts.logic)

        if reset:
            init = True
            trans = True
            invar = True
            ftrans = True

            if (ts.init is None) or (ts.init == TRUE()):
                init = False

            if (ts.invar is None) or (ts.invar == TRUE()):
                invar = False

            if (ts.trans is None) or (ts.trans == TRUE()):
                trans = False

            if (ts.ftrans is None) or (ts.ftrans == {}):
                ftrans = False

            self.reset_formulae(init=init, invar=invar, trans=trans, ftrans=ftrans)

    def remove_ts(self, name):
        self.tss = set([ts for ts in self.tss if name not in ts.comment])

        self.reset_formulae()

    def add_assumption(self, assumption):
        if self.assumptions is None:
            self.assumptions = set([])

        self.assumptions.add(assumption)

    def add_lemma(self, lemma):
        if self.lemmas is None:
            self.lemmas = set([])

        self.lemmas.add(lemma)

    def is_input(self, var):
        return var in self.input_vars

    def remove_invars(self):
        for ts in self.tss:
            ts.remove_invar()

    def single_init(self, rebuild=False):
        if (self._s_init is None) or rebuild:
            self._s_init = TRUE()
            for ts in self.tss:
                init = ts.init
                if init is not None:
                    self._s_init = And(self._s_init, init)

        return self._s_init

    def single_trans(self, rebuild=False, include_ftrans=True):
        if (self._s_trans is None) or (rebuild):
            self._s_trans = TRUE()
            self._s_ftrans_t = TRUE()
            for ts in self.tss:
                ftrans = ts.compile_ftrans()
                if ftrans is not None:
                    self._s_ftrans_t = And(self._s_ftrans_t, ftrans[1])
                trans = ts.trans
                if trans is not None:
                    self._s_trans = And(self._s_trans, trans)

        atrans = TRUE()
        ftrans = TRUE()

        if self.assumptions is not None:
            atrans = And([a for a in self.assumptions if TS.has_next(a)])

        if include_ftrans and (self._s_ftrans_t is not None):
            ftrans = self._s_ftrans_t

        return And(self._s_trans, ftrans, atrans)

    def single_ftrans(self, rebuild=False):
        if (self._s_ftrans is None) or (rebuild):
            self._s_ftrans = {}
            for ts in self.tss:
                if ts.ftrans is not None:
                    for var, cond_assign_list in ts.ftrans.items():
                        self._s_ftrans[var] = cond_assign_list

        return self._s_ftrans

    def single_invar(self, rebuild=False, include_ftrans=True):
        if (self._s_invar is None) or (rebuild):
            self._s_invar = TRUE()
            self._s_ftrans_i = TRUE()
            for ts in self.tss:
                finvar = ts.compile_ftrans()
                if finvar is not None:
                    self._s_ftrans_i = And(self._s_ftrans_i, finvar[0])
                invar = ts.invar
                if invar is not None:
                    self._s_invar = And(self._s_invar, invar)

        ainvar = TRUE()
        ftrans = TRUE()

        if self.assumptions is not None:
            ainvar = And([a for a in self.assumptions if not TS.has_next(a)])

        if include_ftrans and (self._s_ftrans_i is not None):
            ftrans = self._s_ftrans_i

        return And(self._s_invar, ftrans, ainvar)

    def reset_formulae(self, init=True, invar=True, trans=True, ftrans=True):
        if init:
            self._s_init = None
        if trans:
            self._s_trans = None
        if ftrans:
            self._s_ftrans_t = None
            self._s_ftrans_i = None
            self._s_ftrans = None
        if invar:
            self._s_invar = None

        for sub in self.subs:
            sub[2].reset_formulae(init, invar, trans, ftrans)

    def reset_flatten(self):
        self.is_flatten = False
        self._s_init = None
        self._s_invar = None
        self._s_trans = None
        self._s_ftrans = None

        self.remove_ts(FLATTEN)

        self.reset_formulae()

        for sub in self.subs:
            sub[2].reset_flatten()

    def combine(self, other_hts):
        for ts in other_hts.tss:
            self.add_ts(ts, add_vars=False, reset=False)

        for v in other_hts.state_vars:
            if v not in self.input_vars:
                self.state_vars.add(v)

        for v in other_hts.input_vars:
            self.input_vars.add(v)

        for v in other_hts.output_vars:
            if v not in self.input_vars:
                self.output_vars.add(v)

        for v in other_hts.vars:
            self.add_var(v)

        if other_hts.assumptions is not None:
            for assumption in other_hts.assumptions:
                self.add_assumption(assumption)

        if other_hts.lemmas is not None:
            for lemma in other_hts.lemmas:
                self.add_lemma(lemma)

        self.reset_formulae()

    def newname(self, varname, path=[]):
        ret = varname.replace(self.name, ".".join(path)).strip()
        if ret[0] == ".":
            ret = ret[1:]
        return ret

    def get_TS(self, ftrans=False):
        ts = TS()
        ts.vars = self.vars
        ts.state_vars = self.state_vars
        ts.input_vars = self.input_vars
        ts.output_vars = self.output_vars
        ts.init = self.single_init()
        ts.invar = self.single_invar(include_ftrans=not ftrans)
        ts.trans = self.single_trans(include_ftrans=not ftrans)
        ts.ftrans = self.single_ftrans()

        return ts

    def flatten(self, cleanup=True):
        if cleanup:
            tmp_input_vars = set([v for v in self.input_vars])
            tmp_output_vars = set([v for v in self.output_vars])
        vardic = dict([(v.symbol_name(), v) for v in self.vars])
        output_vars = self._flatten_rec(vardic)[3]
        if cleanup:
            self.input_vars = tmp_input_vars
            self.output_vars = tmp_output_vars
            for var in output_vars:
                if var not in self.output_vars:
                    self.add_state_var(var)

        self.reset_formulae()

    def _flatten_rec(self, vardic, path=[]):
        self.is_flatten = True

        def full_path(name, path):
            ret = ".".join(path+[name])
            if ret[0] == ".":
                return ret[1:]
            return ret

        for sub in self.subs:
            instance, actual, module = sub
            module.is_flatten = True
            formal = module.params

            ts = TS(FLATTEN)

            (ts.vars, \
             ts.state_vars, \
             ts.input_vars, \
             ts.output_vars, \
             ts.init, \
             ts.trans, \
             ts.ftrans, \
             ts.invar) = module._flatten_rec(vardic, path+[instance])

            self.add_ts(ts, reset=False)

            links = {}
            for i in range(len(actual)):
                # Unset parameter
                if actual[i] == None:
                    continue
                if type(actual[i]) == str:
                    local_expr = vardic[full_path(actual[i], path)]
                else:
                    local_vars = [(v.symbol_name(), v.symbol_name().replace(self.name, ".".join(path))) \
                                  for v in get_free_variables(actual[i])]
                    local_expr = substitute(actual[i], dict(local_vars))
                module_var = sub[2].newname(formal[i].symbol_name(), path+[sub[0]])
                assert sub[2].name != ""
                if module_var not in vardic:
                    modulevar = Symbol(module_var, formal[i].symbol_type())
                    self.vars.add(modulevar)
                    vardic[module_var] = modulevar
                if vardic[module_var] in self.output_vars:
                    links[local_expr] = [(TRUE(), vardic[module_var])]
                else:
                    links[vardic[module_var]] = [(TRUE(), local_expr)]

            ts = TS(LINKS)
            ts.ftrans = links
            self.add_ts(ts, reset=False)

        s_init = self.single_init()
        s_invar = self.single_invar(include_ftrans=False)
        s_trans = self.single_trans(include_ftrans=False)

        replace_dic = dict([(v.symbol_name(), self.newname(v.symbol_name(), path)) for v in self.vars] + \
                           [(TS.get_prime_name(v.symbol_name()), self.newname(TS.get_prime_name(v.symbol_name()), path)) \
                            for v in self.vars])

        substitute_dic = {}
        def substitute_mem(f, dic):
            if f in substitute_dic:
                return substitute_dic[f]
            ret = substitute(f, dic)
            substitute_dic[f] = ret
            return ret

        s_init = substitute_mem(s_init, replace_dic)
        s_invar = substitute_mem(s_invar, replace_dic)
        s_trans = substitute_mem(s_trans, replace_dic)

        s_ftrans = {}

        local_vars = []
        local_state_vars = []
        local_input_vars = []
        local_output_vars = []

        single_ftrans = self.single_ftrans()

        for var in list(self.vars):
            newsym = Symbol(replace_dic[var.symbol_name()], var.symbol_type())

            local_vars.append(newsym)
            if var in self.state_vars:
                local_state_vars.append(newsym)
            if var in self.input_vars:
                local_input_vars.append(newsym)
            if var in self.output_vars:
                local_output_vars.append(newsym)

            if var in single_ftrans:
                cond_assign_list = single_ftrans[var]
                s_ftrans[newsym] = [(substitute_mem(condition, replace_dic), \
                                     substitute_mem(value, replace_dic)) \
                                    for (condition, value) in cond_assign_list]
                del(single_ftrans[var])

        for var, cond_assign_list in single_ftrans.items():
            s_ftrans[substitute_mem(var, replace_dic)] = [(substitute_mem(condition, replace_dic), \
                                                           substitute_mem(value, replace_dic)) \
                                                          for (condition, value) in cond_assign_list]

        return (local_vars, local_state_vars, local_input_vars, local_output_vars, s_init, s_trans, s_ftrans, s_invar)

    def __copy__(self):
        cls = self.__class__
        new_hts = cls.__new__(cls)
        new_hts.__dict__.update(self.__dict__)
        new_hts.tss = set(new_hts.tss)
        new_hts.subs = list(new_hts.subs)
        return new_hts

    def __repr__(self):
        ret = []

        ret.append("Name: %s"%self.name)
        ret.append("Vars: %s"%str(self.vars))
        ret.append("Subs: %s"%str(self.subs))

        return "; ".join(ret)

    def print_statistics(self, name=None, detailed=False):

        def type_vars(varset, prefix=""):
            ret = {}
            totbits = 0
            for v in varset:
                stype = v.symbol_type()
                if stype not in ret:
                    ret[stype] = 0
                ret[stype] += 1

                if stype.is_bv_type():
                    totbits += stype.width

            rlist = [(ret[t], str(t)) for t in ret]
            rlist.sort()
            rlist.reverse()
            rstr = []
            for rtype in rlist:
                rstr.append("%s%s:\t%d"%(prefix, rtype[1], rtype[0]))

            rstr.append("%sTotal Bits: %d"%(prefix, totbits))
            return "\n".join(rstr)

        stat = []
        stat.append("Statistics (%s):"%(self.name if name is None else name))
        stat.append("  Variables:\t%s"%(len(self.vars)))
        if detailed:
            stat.append(type_vars(self.vars, "   - "))
        stat.append("  StateVars:\t%s"%(len(self.state_vars)))
        if detailed:
            stat.append(type_vars(self.state_vars, "   - "))
        stat.append("  Inputs:\t%s"%(len(self.input_vars)))
        if detailed:
            stat.append(type_vars(self.input_vars, "   - "))
        stat.append("  Outputs:\t%s"%(len(self.output_vars)))
        if detailed:
            stat.append(type_vars(self.output_vars, "   - "))
        return "\n".join(stat)

class TS(object):

    vars = None
    state_vars = None
    input_vars = None
    output_vars = None
    hidden_vars = None

    init = None
    trans = None
    invar = None
    ftrans = None

    comment = None
    logic = None

    def __init__(self, comment=""):
        self.vars = set([])
        self.state_vars = set([])
        self.input_vars = set([])
        self.output_vars = set([])
        self.hidden_vars = set([])
        self.init = TRUE()
        self.trans = TRUE()
        self.invar = TRUE()
        self.ftrans = None

        self.comment = comment
        self.logic = L_BV

    def __repr__(self):
        return "V: %s\nSV: %s\nI: %s\nT: %s\nC: %s"%(str(self.vars), str(self.state_vars), str(self.init), str(self.trans), str(self.invar))

    def remove_invar(self):
        if self.invar is not None:
            self.trans = And([self.trans, self.invar, TS.to_next(self.invar)])
            self.init = And(self.init, self.invar)

        self.invar = None

    def apply_var_prefix(self, prefix):
        p_vars = set([Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.vars])
        p_state_vars = set([Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.state_vars])
        p_input_vars = set([Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.input_vars])
        p_output_vars = set([Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.output_vars])
        p_hidden_vars = set([Symbol(apply_prefix(v.symbol_name(), prefix), v.symbol_type()) for v in self.hidden_vars])
        remapdic = dict([(v.symbol_name(), apply_prefix(v.symbol_name(), prefix)) for v in self.vars]+\
                        [(TS.get_prime(v).symbol_name(), apply_prefix(TS.get_prime(v).symbol_name(), prefix)) for v in self.vars])

        p_init = substitute(self.init, remapdic)
        p_trans = substitute(self.trans, remapdic)
        p_invar = substitute(self.invar, remapdic)

        p_ftrans = None

        if self.ftrans is not None:
            p_ftrans = {}
            for var, cond_assign_list in self.ftrans.items():
                p_ftrans[substitute(var, remapdic)] = [(substitute(condition, remapdic), substitute(value, remapdic)) for (condition, value) in cond_assign_list]

        self.vars = p_vars
        self.state_vars = p_state_vars
        self.input_vars = p_input_vars
        self.output_vars = p_output_vars
        self.hidden_vars = p_hidden_vars
        self.init = p_init
        self.trans = p_trans
        self.ftrans = p_ftrans
        self.invar = p_invar

        return self

    def set_behavior(self, init, trans, invar):
        self.init = init
        self.trans = trans
        self.invar = invar

    def add_var(self, var):
        self.vars.add(var)

    def add_hidden_var(self, var):
        self.hidden_vars.add(var)

    def add_state_var(self, var):
        self.state_vars.add(var)
        if var.symbol_type().is_array_type():
            self.logic = L_ABV
        self.vars.add(var)

    def add_input_var(self, var):
        self.input_vars.add(var)
        self.vars.add(var)

    def add_output_var(self, var):
        self.output_vars.add(var)
        self.vars.add(var)

    def add_func_trans(self, var, cond_assign_list):
        if self.ftrans is None:
            self.ftrans = {}

        assert var not in self.ftrans

        self.ftrans[var] = cond_assign_list

        self._s_ftrans = None

    def compile_ftrans(self):
        if self.ftrans is None:
            return None

        ret_trans = TRUE()
        ret_invar = TRUE()

        use_ites = False

        if use_ites:
            for var, cond_assign_list in self.ftrans.items():
                if TS.has_next(var):
                    ite_list = TS.to_prev(var)
                else:
                    ite_list = var
                for (condition, value) in reversed(cond_assign_list):
                    if condition == TRUE():
                        ite_list = value
                    else:
                        ite_list = Ite(condition, value, ite_list)

                if TS.has_next(ite_list):
                    ret_trans = And(ret_trans, EqualsOrIff(var, ite_list))
                else:
                    ret_invar = And(ret_invar, EqualsOrIff(var, ite_list))
        else:
            for var, cond_assign_list in self.ftrans.items():
                effects = []
                all_neg_cond = []
                for (condition, value) in cond_assign_list:
                    effects.append(simplify(Implies(condition, EqualsOrIff(var, value))))
                    all_neg_cond.append(Not(condition))

                if not TS.has_next(var) and not TS.has_next(condition):
                    ret_invar = And(ret_invar, And(effects))
                else:
                    ret_trans = And(ret_trans, And(effects))

                if TS.has_next(var):
                    no_change = EqualsOrIff(var, TS.to_prev(var))
                    ret_trans = And(ret_trans, simplify(Implies(And(all_neg_cond), no_change)))

        return (ret_invar, ret_trans)

    @staticmethod
    def is_prime(v):
        return v.symbol_name()[-len(NEXT):] == NEXT

    @staticmethod
    def is_timed(v):
        varname = v.symbol_name()
        return (AT in varname) and (ATP not in varname)

    @staticmethod
    def is_ptimed(v):
        return ATP in v.symbol_name()

    @staticmethod
    def is_prev(v):
        return v.symbol_name()[-len(PREV):] == PREV

    @staticmethod
    def get_ref_var(v):
        # Optimization
        if CPREF not in v.symbol_name():
            return v

        if TS.is_prime(v):
            return Symbol(v.symbol_name()[:-len(NEXT)], v.symbol_type())
        if TS.is_prev(v):
            return Symbol(v.symbol_name()[:-len(PREV)], v.symbol_type())
        if TS.is_ptimed(v):
            varname = v.symbol_name()
            return Symbol(varname[:varname.find(ATP)], v.symbol_type())
        if TS.is_timed(v):
            varname = v.symbol_name()
            return Symbol(varname[:varname.find(AT)], v.symbol_type())
        return v

    @staticmethod
    def is_prime_name(varname):
        return varname[-len(NEXT):] == NEXT

    @staticmethod
    def is_timed_name(varname):
        return (AT in varname) and (ATP not in varname)

    @staticmethod
    def is_ptimed_name(varname):
        return ATP in varname

    @staticmethod
    def is_prev_name(varname):
        return varname[-len(PREV):] == PREV

    @staticmethod
    def get_ref_name(name):
        if TS.is_prime_name(name):
            return name[:-len(NEXT)]
        if TS.is_prev_name(name):
            return name[:-len(PREV)]
        if TS.is_ptimed_name(name):
            return name[:name.find(ATP)]
        if TS.is_timed_name(name):
            return name[:name.find(AT)]
        return name

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
    def get_time(v):
        if not(TS.is_timed(v) or TS.is_ptimed(v)):
            return None
        varname = v.symbol_name()
        if TS.is_ptimed(v):
            return -int(varname[varname.find(ATP)+len(ATP):])

        return int(varname[varname.find(AT)+len(AT):])

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
            vname = TS.get_ref_name(v.symbol_name())
            varmap.append((vname,TS.get_prime_name(vname)))
            varmap.append((TS.get_prev_name(vname),vname))
        return substitute(formula, dict(varmap))

    @staticmethod
    def to_prev(formula):
        varmap = []
        for v in get_free_variables(formula):
            vname = TS.get_ref_name(v.symbol_name())
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
