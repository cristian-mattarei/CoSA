# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pyparsing import Literal, Word, nums, alphas, OneOrMore, ZeroOrMore, Optional, restOfLine, LineEnd, Combine, White, Group, SkipTo, lineEnd
from pysmt.shortcuts import TRUE, And, Or, Symbol, BV, EqualsOrIff, Implies
from pysmt.typing import BOOL, BVType

from cosa.representation import HTS, TS
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import quote_names
from cosa.encoders.template import ModelParser
from cosa.encoders.formulae import StringParser

T_NL = "\n"

T_EQ = "="
T_US = "_"
T_MIN = "-"
T_DOT = "."
T_SC = ";"
T_CM = ","
T_CL = ":"
T_MIN = "-"
T_PLUS = "+"
T_EQ = "="
T_LT = "<"
T_LTE = "<="
T_NEQ = "!="
T_SP = " "
T_IMPL = "->"
T_BOOLSYM = "|&"
T_ITE = "?:"
T_NEG = "!"

T_OP = "("
T_CP = ")"
T_OB = "["
T_CB = "]"

T_VAR = "VAR"
T_STATE = "STATE"
T_INPUT = "INPUT"
T_OUTPUT = "OUTPUT"
T_INIT = "INIT"
T_TRANS = "TRANS"
T_FTRANS = "FUNC"
T_INVAR = "INVAR"
T_DEF = "DEF"

T_BV = "BV"
T_BOOL = "Bool"

T_COM = "#"
T_TRUE = "True"
T_FALSE = "False"

P_COMMENT = "comment"
P_EMPTY = "empty"
P_VARNAME = "varname"
P_FORMULA = "formula"
P_FORMULAE = "formulae"
P_VARDEFS = "vardefs"
P_STATEDEFS = "statedefs"
P_INPUTDEFS = "inputdefs"
P_OUTPUTDEFS = "outputdefs"
P_VARS = "var"
P_STATES = "state"
P_INPUTS = "input"
P_OUTPUTS = "output"
P_INIT = "init"
P_TRANS = "trans"
P_INVAR = "invar"
P_VARTYPE = "vartype"
P_VARTYPEDEF = "vartypedef"
P_PARDEF = "pardef"
P_VARSIZE = "varsize"
P_STS = "sts"
P_STSS = "stss"
P_MODTYPE = "module"
P_MODDEF = "moduledef"

MAIN = ""

count = 0

class STSModule(object):

    vars = None
    states = None
    inputs = None
    outputs = None
    pars = None
    init = None
    invar = None
    trans = None
    subs = None

    def __init__(self, name, vars, states, inputs, outputs, pars, init, invar, trans, subs=[]):
        self.name = name
        self.vars = vars
        self.states = states
        self.inputs = inputs
        self.outputs = outputs
        self.init = init
        self.invar = invar
        self.trans = trans
        self.subs = subs
        self.pars = pars

    def __repr__(self):
        return "%s: %s, %s"%(self.name, self.var, self.par)

class SymbolicTSParser(ModelParser):
    parser = None
    extensions = ["sts"]
    name = "STS"
    
    def __init__(self):
        self.parser = self.__init_parser()
        self.parser.ignore(T_COM + SkipTo(lineEnd))

    def parse_file(self, strfile, config, flags=None):
        with open(strfile, "r") as f:
            return self.parse_string(f.read())

    def is_available(self):
        return True

    def get_model_info(self):
        return None
     
    def _split_list(self, lst, delimiter):
        ret = []
        sub = []
        for el in lst:
            if el != delimiter:
                sub.append(el)
            else:
                ret.append(sub)
                sub = []

        if sub != []:
            ret.append(sub)

        return ret
        
    def parse_string(self, strinput):
        lines = []
        pstring = self.parser.parseString(strinput, parseAll=True)

        hts = HTS("STS")
        invar_props = []
        ltl_props = []
        
        modules = []
        modulesdic = {}

        name = MAIN
        mainmodule = None
        
        for psts in pstring.stss:

            var_str = []
            state_str = []
            input_str = []
            output_str = []
            sub_str = []
            par_str = []
            init_str = []
            trans_str = []
            invar_str = []

            if len(psts.moduledef) > 0:
                name = psts.moduledef[1]

            if len(psts.pardef) > 0:
                vardefs = psts.pardef

                for vardef in self._split_list(vardefs, T_CM):
                    varname = vardef[0]
                    vartype = vardef[2]
                    varpar = vardef[4:-1] if vartype != T_BOOL else None

                    par_str.append((varname, vartype, varpar))

            if P_VARDEFS in dict(psts):
                vardefs = list(dict(psts.var)[P_VARDEFS])

                for vardef in self._split_list(vardefs, T_SC):
                    varname = vardef[0]
                    if varname[0] == "'":
                         varname = varname[1:-1]

                    vartype = vardef[2]
                    varpar = vardef[4:-1] if vartype != T_BOOL else None

                    if vartype in (T_BV, T_BOOL):
                        var_str.append((varname, vartype, varpar))
                    else:
                        sub_str.append((varname, vartype, self._split_list(varpar, T_CM)))

            if P_STATEDEFS in dict(psts):
                statedefs = list(dict(psts.state)[P_STATEDEFS])

                for statedef in self._split_list(statedefs, T_SC):
                    statename = statedef[0]
                    if statename[0] == "'":
                         statename = statename[1:-1]

                    statetype = statedef[2]
                    statepar = statedef[4:-1] if statetype != T_BOOL else None

                    state_str.append((statename, statetype, statepar))

            if P_INPUTDEFS in dict(psts):
                inputdefs = list(dict(psts.input)[P_INPUTDEFS])

                for inputdef in self._split_list(inputdefs, T_SC):
                    inputname = inputdef[0]
                    if inputname[0] == "'":
                         inputname = inputname[1:-1]

                    inputtype = inputdef[2]
                    inputpar = inputdef[4:-1] if inputtype != T_BOOL else None

                    input_str.append((inputname, inputtype, inputpar))

            if P_OUTPUTDEFS in dict(psts):
                outputdefs = list(dict(psts.output)[P_OUTPUTDEFS])

                for outputdef in self._split_list(outputdefs, T_SC):
                    outputname = outputdef[0]
                    if outputname[0] == "'":
                         outputname = outputname[1:-1]

                    outputtype = outputdef[2]
                    outputpar = outputdef[4:-1] if outputtype != T_BOOL else None

                    output_str.append((outputname, outputtype, outputpar))
                    
            if P_INIT in dict(psts):
                inits = list(dict(psts.init)[P_FORMULAE])
                for i in range(0, len(inits), 2):
                    init_str.append(inits[i])

            if P_TRANS in dict(psts):
                transs = list(dict(psts.trans)[P_FORMULAE])
                for i in range(0, len(transs), 2):
                    trans_str.append(transs[i])

            if P_INVAR in dict(psts):
                invars = list(dict(psts.invar)[P_FORMULAE])
                for i in range(0, len(invars), 2):
                    invar_str.append(invars[i])

            module = STSModule(name, var_str, state_str, input_str, output_str, par_str, init_str, invar_str, trans_str, sub_str)
            modules.append(module)

            if name == MAIN:
                mainmodule = module
            else:
                modulesdic[name] = module
                
            #hts.add_ts(self.generate_STS(var_str, init_str, invar_str, trans_str))

        hts = self.generate_HTS(mainmodule, modulesdic)
        hts.flatten()
        return (hts, invar_props, ltl_props)
        
    def __init_parser(self):

        varname = (Combine(Literal("'")+Word(alphas+nums+T_US+T_MIN+T_DOT+"$"+"["+"]"+":")+Literal("'")) | Word(alphas+nums+T_US+T_MIN+T_DOT))(P_VARNAME)

        comment = Group(T_COM + restOfLine + LineEnd())(P_COMMENT)
        emptyline = Group(ZeroOrMore(White(' \t')) + LineEnd())(P_EMPTY)

        varsize = (Word(nums))(P_VARSIZE)
        parlist = (ZeroOrMore(varname)+ZeroOrMore((Literal(T_CM) + varname)))
        modtype = (Word(alphas+T_US+nums) + Literal(T_OP) + parlist + Literal(T_CP))(P_MODTYPE)
        basictype = (Literal(T_BV) + Literal(T_OP) + varsize + Literal(T_CP)) | Literal(T_BOOL)
        vartype = (basictype | modtype)(P_VARTYPE)
        vartypedef = (vartype)(P_VARTYPEDEF)
        vardef = varname + Literal(T_CL) + vartypedef + Literal(T_SC)

        basicvardef = (varname + Literal(T_CL) + basictype)(P_VARTYPEDEF)
        parlistdef = (ZeroOrMore(basicvardef)+ZeroOrMore((Literal(T_CM) + basicvardef)))(P_PARDEF)
        moddef = (Literal(T_DEF) + Word(alphas+T_US+nums) + Literal(T_OP) + parlistdef + Literal(T_CP) + Literal(T_CL))(P_MODDEF)
        
        operators = T_NEG+T_MIN+T_PLUS+T_EQ+T_NEQ+T_LT+T_LTE+T_IMPL+T_BOOLSYM+T_ITE
        formula = (Word(alphas+nums+T_US+T_SP+T_DOT+T_OP+T_CP+T_OB+T_CB+"'"+operators) + Literal(T_SC))(P_FORMULA)

        vardefs = (Literal(T_VAR) + (OneOrMore(vardef)(P_VARDEFS)))(P_VARS)
        statedefs = (Literal(T_STATE) + (OneOrMore(vardef)(P_STATEDEFS)))(P_STATES)
        inputdefs = (Literal(T_INPUT) + (OneOrMore(vardef)(P_INPUTDEFS)))(P_INPUTS)
        outputdefs = (Literal(T_OUTPUT) + (OneOrMore(vardef)(P_OUTPUTDEFS)))(P_OUTPUTS)
        inits = (Literal(T_INIT) + (OneOrMore(formula))(P_FORMULAE))(P_INIT)
        transs = (Literal(T_TRANS) + (OneOrMore(formula))(P_FORMULAE))(P_TRANS)
        invars = (Literal(T_INVAR) + (OneOrMore(formula))(P_FORMULAE))(P_INVAR)
        
        sts = Group((Optional(moddef) + OneOrMore(vardefs | statedefs | inputdefs | outputdefs | inits | transs | invars | emptyline)))(P_STS)

        return (OneOrMore(sts))(P_STSS)

    def _define_var(self, var, prefix=""):
        varname, (vartype, size) = var
        fullname = self._concat_names(prefix, varname)    
        
        if vartype == T_BV:
            return Symbol(fullname, BVType(int(size[0])))

        if vartype == T_BOOL:
            return Symbol(fullname, BOOL)
        
        Logger.error("Unsupported type: %s"%vartype)

    def _get_type(self, strtype):
        (vartype, size) = strtype
        
        if vartype == T_BV:
            return BVType(int(size[0]))

        if vartype == T_BOOL:
            return BOOL
        
        Logger.error("Unsupported type: %s"%vartype)

    def _concat_names(self, prefix, name):
        return ".".join([x for x in [prefix,name] if x != ""])
        
    def _collect_sub_variables(self, module, modulesdic, path=[], varlist=[], statelist=[], inputlist=[], outputlist=[]):
        
        for var in module.vars+module.pars:
            varlist.append((".".join(path+[str(var[0])]), var[1:]))

        for var in module.states:
            statelist.append((".".join(path+[str(var[0])]), var[1:]))

        for var in module.inputs:
            inputlist.append((".".join(path+[str(var[0])]), var[1:]))

        for var in module.outputs:
            outputlist.append((".".join(path+[str(var[0])]), var[1:]))
            
        for sub in module.subs:
            (varlist, statelist, inputlist, outputlist) = self._collect_sub_variables(modulesdic[sub[1]], modulesdic, path + [sub[0]], varlist, statelist, inputlist, outputlist)

        return (varlist, statelist, inputlist, outputlist)

    def _check_parameters(self, module, modulesdic, vars_):

        vartypes = dict([(v.symbol_name(), v.symbol_type()) for v in vars_])

        for sub in module.subs:
            formal_pars = [self._get_type(t[1:]) for t in modulesdic[sub[1]].pars]
            actual_pars = [vartypes[self._concat_names(module.name, v[0])] for v in sub[2]]
            
            if formal_pars != actual_pars:
                Logger.error("Not matching types for instance \"%s\" of type \"%s\""%(sub[0], sub[1]))
    
    def generate_HTS(self, module, modulesdic):
        hts = HTS(module.name)
        ts = TS("TS %s"%module.name)
        
        init = []
        trans = []
        invar = []
        params = []

        sparser = StringParser()

        (vars, states, inputs, outputs) = self._collect_sub_variables(module, modulesdic, path=[], varlist=[])

        for var in vars:
            ts.add_var(self._define_var(var, module.name))

        for var in states:
            ts.add_state_var(self._define_var(var, module.name))
            
        for var in inputs:
            ts.add_input_var(self._define_var(var, module.name))

        for var in outputs:
            ts.add_output_var(self._define_var(var, module.name))
        
        self._check_parameters(module, modulesdic, ts.vars)

        for par in module.pars:
            hts.add_param(self._define_var((par[0], tuple(par[1:])), module.name))

        for init_s in module.init:
            formula = sparser.parse_formula(quote_names(init_s, module.name), False)
            init.append(formula)

        for invar_s in module.invar:
            formula = sparser.parse_formula(quote_names(invar_s, module.name), False)
            invar.append(formula)

        for trans_s in module.trans:
            formula = sparser.parse_formula(quote_names(trans_s, module.name), False)
            trans.append(formula)

        for sub in module.subs:
            hts.add_sub(sub[0], self.generate_HTS(modulesdic[sub[1]], modulesdic), tuple([v[0] for v in sub[2]]))
            
        ts.init = And(init)
        ts.invar = And(invar)
        ts.trans = And(trans)

        hts.add_ts(ts)
        
        return hts
        
    def generate_STS(self, var_str, init_str, invar_str, trans_str):
        ts = TS("Additional system")
        init = []
        trans = []
        invar = []

        sparser = StringParser()

        for var in var_str:
            ts.add_state_var(self._define_var(var))

        for init_s in init_str:
            init.append(sparser.parse_formula(init_s))

        for invar_s in invar_str:
            invar.append(sparser.parse_formula(invar_s))

        for trans_s in trans_str:
            trans.append(sparser.parse_formula(trans_s))
            
        ts.init = And(init)
        ts.invar = And(invar)
        ts.trans = And(trans)
        
        return ts
    
    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

    def get_extensions(self):
        return self.extensions

    @staticmethod        
    def get_extensions():
        return SymbolicTSParser.extensions
    
class SymbolicSimpleTSParser(ModelParser):
    parser = None
    extensions = ["ssts"]
    name = "SimpleSTS"
    
    def __init__(self):
        pass

    @staticmethod        
    def get_extensions():
        return SymbolicSimpleTSParser.extensions

    def get_model_info(self):
        return None
    
    def is_available(self):
        return True
    
    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name
    
    def parse_file(self, strfile, config, flags=None):
        with open(strfile, "r") as f:
            lines = (f.read().replace("\\\n","")).splitlines(True)
            return self.parse_string(lines)

    def _define_var(self, varname, vartype):
        if vartype == T_BOOL:
            return Symbol(varname, BOOL)

        if vartype[0] == T_BV:
            vartype, size = vartype[0], vartype[1]
            return Symbol(varname, BVType(int(size)))
        
        Logger.error("Unsupported type: %s"%vartype)
        
    def parse_string(self, lines):

        [none, var, state, input, output, init, invar, trans, ftrans] = range(9)
        section = none
        
        inits = TRUE()
        invars = TRUE()
        transs = TRUE()
        ftranss = {}

        sparser = StringParser()

        count = 0
        vars = set([])
        states = set([])
        inputs = set([])
        outputs = set([])
        invar_props = []
        ltl_props = []
        
        for line in lines:
            count += 1

            if (line.strip() in ["","\n"]) or line[0] == T_COM:
                continue

            if T_VAR == line[:len(T_VAR)]:
                section = var
                continue

            if T_STATE == line[:len(T_STATE)]:
                section = state
                continue

            if T_INPUT == line[:len(T_INPUT)]:
                section = input
                continue

            if T_OUTPUT == line[:len(T_OUTPUT)]:
                section = output
                continue
            
            if T_INIT == line[:len(T_INIT)]:
                section = init
                continue

            if T_INVAR == line[:len(T_INVAR)]:
                section = invar
                continue

            if T_TRANS == line[:len(T_TRANS)]:
                section = trans
                continue

            if T_FTRANS == line[:len(T_FTRANS)]:
                section = ftrans
                continue
            
            if section in [var, state, input, output]:
                line = line[:-2].replace(" ","").split(":")
                varname, vartype = line[0], (line[1][:-1].split("(")) if "(" in line[1] else line[1]
                if varname[0] == "'":
                    varname = varname[1:-1]
                vardef = self._define_var(varname, vartype)

                vars.add(vardef)
                if section == state:
                    states.add(vardef)
                if section == input:
                    inputs.add(vardef)
                if section == output:
                    outputs.add(vardef)

            if section in [init, invar, trans]:
                qline = quote_names(line[:-2], replace_ops=False)
                    
            if section == init:
                inits = And(inits, sparser.parse_formula(qline))

            if section == invar:
                invars = And(invars, sparser.parse_formula(qline))

            if section == trans:
                transs = And(transs, sparser.parse_formula(qline))

            if section == ftrans:
                strvar = line[:line.find(":=")]
                var = sparser.parse_formula(quote_names(strvar, replace_ops=False))
                cond_ass = line[line.find(":=")+2:].strip()
                ftranss[var] = []

                for cond_as in cond_ass.split("{"):
                    if cond_as == "":
                        continue
                    cond = cond_as[:cond_as.find(",")]
                    ass = cond_as[cond_as.find(",")+1:cond_as.find("}")]
                    ftranss[var].append((sparser.parse_formula(quote_names(cond, replace_ops=False)), sparser.parse_formula(quote_names(ass, replace_ops=False))))

        hts = HTS("STS")
        ts = TS()

        ts.vars = vars
        ts.state_vars = states
        ts.input_vars = inputs
        ts.output_vars = outputs
        ts.init = inits
        ts.invar = invars
        ts.trans = transs
        ts.ftrans = ftranss
        
        hts.add_ts(ts)

        return (hts, invar_props, ltl_props)
