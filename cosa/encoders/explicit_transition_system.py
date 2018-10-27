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
from pysmt.shortcuts import TRUE, FALSE, And, Or, Symbol, BV, EqualsOrIff, Implies, BVULE
from pysmt.typing import BOOL, BVType

from cosa.representation import HTS, TS
from cosa.printers.template import HIDDEN_VAR
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import get_free_variables
from cosa.encoders.template import ModelParser

import math

T_NL = "\n"

T_EQ = "="
T_US = "_"
T_MIN = "-"
T_DOT = "."
T_I = "I"
T_CL = ":"

T_A = "A"
T_B = "B"
T_C = "C"
T_D = "D"
T_E = "E"
T_F = "F"

T_S = "S"
T_COM = "#"
T_ARROW = "->"
T_TRUE = "True"
T_FALSE = "False"

P_COMMENT = "comment"
P_EMPTY = "empty"
P_STATE = "state"
P_VARNAME = "varname"
P_SNAME = "sname"
P_VALUE = "value"
P_TYPE = "type"
P_START = "start"
P_END = "end"
P_INIT = "init"
P_TRANS = "trans"
P_ID = "id"

STATE_ID = "state_id"

class ExplicitTSParser(ModelParser):
    parser = None
    extensions = ["ets"]
    name = "ETS"
    
    state_id = 0

    def __init__(self):
        self.parser = self.__init_parser()

    def parse_file(self, strfile, config, flags=None):
        with open(strfile, "r") as f:
            return self.parse_string(f.read())

    def is_available(self):
        return True

    def get_model_info(self):
        return None
     
    def parse_string(self, strinput):
        lines = []
        for line in strinput.split(T_NL):
            pline = self.parser.parseString(line, parseAll=True)
            lines.append(pline)

        return self.generate_STS(lines)

    def new_state_id(self):
        ExplicitTSParser.state_id += 1
        return HIDDEN_VAR+STATE_ID+str(ExplicitTSParser.state_id)+(HIDDEN_VAR[::-1])

    def __init_parser(self):

        varname = Word(alphas+nums+T_US+T_MIN+T_DOT)(P_VARNAME)
        sname = Word(alphas+nums+T_I+T_S+T_US)(P_SNAME)
        boolvalue = Literal(T_TRUE) | Literal(T_FALSE)
        
        ivalue = Word(nums)
        hexvalue = Word(nums + T_A + T_B + T_C + T_D + T_E + T_F)
        bvvalue = Combine(ivalue + T_US + ivalue)
        
        value = (boolvalue | bvvalue | hexvalue)(P_VALUE)

        comment = (T_COM + restOfLine + LineEnd())(P_COMMENT)
        emptyline = (ZeroOrMore(White(' \t')) + LineEnd())(P_EMPTY)

        init = (Literal(T_I)(P_TYPE) + Literal(T_CL) + ((varname + Literal(T_EQ) + value) | (boolvalue)(P_VALUE)))(P_INIT)
        inits = OneOrMore(init)

        state = (Literal(T_S)(P_TYPE) + ((varname)(P_ID)) + Literal(T_CL) + ((varname + Literal(T_EQ) + value) | (boolvalue)(P_VALUE)))(P_STATE)
        states = OneOrMore(state)

        trans = (sname(P_START) + Literal(T_ARROW) + sname(P_END) + restOfLine)(P_TRANS)
        transs = OneOrMore(trans)
        
        ets = OneOrMore(comment | inits | states | transs | emptyline)

        return ets


    def generate_STS(self, lines):
        ts = TS("Additional system")
        init = TRUE()
        trans = TRUE()
        invar = TRUE()

        states = {}
        assigns = set([])
        varsmap = {}

        def def_var(name, vtype):
            if name in varsmap:
                return varsmap[name]
            var = Symbol(name, vtype)
            ts.add_state_var(var)
            return var
        
        for line in lines:
            if line.comment:
                continue
            if line.init:
                if T_I not in states:
                    states[T_I] = TRUE()

                if line.init.varname != "":
                    (value, typev) = self.__get_value(line.init.value)
                    ivar = def_var(line.init.varname, typev)
                    state = EqualsOrIff(ivar, value)
                else:
                    state = TRUE() if line.init.value == T_TRUE else FALSE()
                
                states[T_I] = And(states[T_I], state)

                # Optimization for the initial state assignment
                init = And(init, state)
                
            state = TRUE()
            if line.state:
                sname = T_S + line.state.id
                if (line.state.varname != ""):
                    (value, typev) = self.__get_value(line.state.value)
                    ivar = def_var(line.state.varname, typev)
                    state = EqualsOrIff(ivar, value)
                    assval = (sname, line.state.varname)
                    if assval not in assigns:
                        assigns.add(assval)
                    else:
                        Logger.error("Double assignment for variable \"%s\" at state \"%s\""%(line.state.varname, sname))
                else:
                    state = TRUE() if line.state.value == T_TRUE else FALSE()
                        
                if sname not in states:
                    states[sname] = TRUE()

                states[sname] = And(states[sname], state)
                
        stateid_width = math.ceil(math.log(len(states))/math.log(2))
        stateid_var = Symbol(self.new_state_id(), BVType(stateid_width))

        init = And(init, EqualsOrIff(stateid_var, BV(0, stateid_width)))
        invar = And(invar, Implies(EqualsOrIff(stateid_var, BV(0, stateid_width)), states[T_I]))
        states[T_I] = EqualsOrIff(stateid_var, BV(0, stateid_width))
        
        count = 1
        state_items = list(states.keys())
        state_items.sort()
        for state in state_items:
            if state == T_I:
                continue
            invar = And(invar, Implies(EqualsOrIff(stateid_var, BV(count, stateid_width)), states[state]))
            states[state] = EqualsOrIff(stateid_var, BV(count, stateid_width))
            count += 1

        transdic = {}

        for line in lines:
            if line.comment:
                continue
                
            if line.trans:
                if states[line.trans.start] not in transdic:
                    transdic[states[line.trans.start]] = []
                transdic[states[line.trans.start]].append(states[line.trans.end])

        for transition in transdic:
            (start, end) = (transition, transdic[transition])
            trans = And(trans, Implies(start, TS.to_next(Or(end))))

        vars_ = [v for v in get_free_variables(trans) if not TS.is_prime(v)]
        vars_ += get_free_variables(init)
        vars_ += get_free_variables(invar)

        invar = And(invar, BVULE(stateid_var, BV(count-1, stateid_width)))
        ts.set_behavior(init, trans, invar)
        ts.add_state_var(stateid_var)

        hts = HTS("ETS")
        hts.add_ts(ts)
        invar_props = []
        ltl_props = []
        
        return (hts, invar_props, ltl_props)
                
    def __get_value(self, value):
        if value == T_FALSE:
            return (FALSE(), BOOL)

        if value == T_TRUE:
            return (TRUE(), BOOL)
        
        if T_US in value:
            width = int(value.split(T_US)[1])
            value = int(value.split(T_US)[0])
        else:
            width = len(value)*4
            value = int(("0x%s"%value).lower(), 0)

        return (BV(value, width), BVType(width))
            
    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

    @staticmethod        
    def get_extensions():
        return ExplicitTSParser.extensions
    
