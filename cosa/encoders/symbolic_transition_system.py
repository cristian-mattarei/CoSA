# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pyparsing import Literal, Word, nums, alphas, OneOrMore, ZeroOrMore, restOfLine, LineEnd, Combine, White
from pysmt.shortcuts import TRUE, And, Or, Symbol, BV, EqualsOrIff, Implies
from pysmt.typing import BOOL, BVType

from cosa.transition_systems import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger

T_NL = "\n"

T_EQ = "="
T_US = "_"
T_MIN = "-"
T_DOT = "."
T_SC = ";"
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
T_INIT = "INIT"
T_TRANS = "TRANS"
T_INVAR = "INVAR"

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
P_VARS = "var"
P_INIT = "init"
P_TRANS = "trans"
P_INVAR = "invar"
P_VARTYPE = "vartype"
P_VARTYPEDEF = "vartypedef"
P_VARSIZE = "varsize"

class SymbolicTSParser(object):
    parser = None
    extension = "sts"
    
    def __init__(self):
        self.parser = self.__init_parser()

    def parse_file(self, strfile, flags=None):
        with open(strfile, "r") as f:
            return self.parse_string(f.read())
        
    def parse_string(self, strinput):
        lines = []
        pstring = self.parser.parseString(strinput, parseAll=True)

        var_str = []
        init_str = []
        trans_str = []
        invar_str = []
        
        vardefs = list(dict(pstring.var)[P_VARDEFS])
        for i in range(0, len(vardefs), 7):
            size = vardefs[i+4] if vardefs[i+2] == T_BV else None
            var_str.append((vardefs[i], vardefs[i+2], size))

        inits = list(dict(pstring.init)[P_FORMULAE])
        for i in range(0, len(inits), 2):
            init_str.append(inits[i])

        if P_TRANS in dict(pstring):
            transs = list(dict(pstring.trans)[P_FORMULAE])
            for i in range(0, len(transs), 2):
                trans_str.append(transs[i])
            
        if P_INVAR in dict(pstring):
            invars = list(dict(pstring.invar)[P_FORMULAE])
            for i in range(0, len(invars), 2):
                invar_str.append(invars[i])
            
        return self.generate_STS(var_str, init_str, invar_str, trans_str)
        
    def __init_parser(self):

        varname = Word(alphas+nums+T_US+T_MIN+T_DOT)(P_VARNAME)

        comment = (T_COM + restOfLine + LineEnd())(P_COMMENT)
        emptyline = (ZeroOrMore(White(' \t')) + LineEnd())(P_EMPTY)

        varsize = (Word(nums))(P_VARSIZE)
        vartype = ((Literal(T_BV) + Literal(T_OP) + varsize + Literal(T_CP)) | Literal(T_BOOL))(P_VARTYPE)
        vartypedef = (vartype)(P_VARTYPEDEF)
        vardef = varname + Literal(T_CL) + vartypedef + Literal(T_SC)
        vardefs = (Literal(T_VAR) + (OneOrMore(vardef)(P_VARDEFS)))(P_VARS)
        
        operators = T_NEG+T_MIN+T_PLUS+T_EQ+T_NEQ+T_LT+T_LTE+T_IMPL+T_BOOLSYM+T_ITE
        formula = (Word(alphas+nums+T_US+T_SP+T_DOT+T_OP+T_CP+T_OB+T_CB+operators) + Literal(T_SC))(P_FORMULA)

        inits = (Literal(T_INIT) + (OneOrMore(formula))(P_FORMULAE))(P_INIT)
        transs = (Literal(T_TRANS) + (OneOrMore(formula))(P_FORMULAE))(P_TRANS)
        invars = (Literal(T_INVAR) + (OneOrMore(formula))(P_FORMULAE))(P_INVAR)
        
        sts = OneOrMore(comment | vardefs | emptyline) + \
              OneOrMore(comment | inits | transs | invars | emptyline)

        return sts

    def _define_var(self, var):
        varname, vartype, size = var
        
        if vartype == T_BV:
            return Symbol(varname, BVType(int(size)))

        if vartype == T_BOOL:
            return Symbol(varname, BOOL)
        
        Logger.error("Unsupported type: %s"%vartype)
    
    def generate_STS(self, var_str, init_str, invar_str, trans_str):
        init = []
        trans = []
        invar = []
        vars_ = []

        sparser = StringParser()

        for var in var_str:
            vars_.append(self._define_var(var))

        for init_s in init_str:
            init.append(sparser.parse_formula(init_s))

        for invar_s in invar_str:
            invar.append(sparser.parse_formula(invar_s))

        for trans_s in trans_str:
            trans.append(sparser.parse_formula(trans_s))
            
        init = And(init)
        invar = And(invar)
        trans = And(trans)

        ts = TS(set(vars_), init, trans, invar)
        ts.comment = "Additional system"

        hts = HTS("STS")
        hts.add_ts(ts)
        
        return hts
                
    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

    def get_extension(self):
        return self.extension

    @staticmethod        
    def get_extension():
        return SymbolicTSParser.extension
    
