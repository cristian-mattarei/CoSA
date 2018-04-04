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
from pysmt.typing import BOOL, _BVType

from cosa.core.transition_system import TS
from cosa.util.logger import Logger
from cosa.printers import HIDDEN

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

STATE_ID = HIDDEN+"state_id"+HIDDEN

class ExplicitTSParser(object):
    parser = None

    def __init__(self):
        self.parser = self.__init_parser()

    def parse(self, strinput):
        lines = []
        for line in strinput.split(T_NL):
            pline = self.parser.parseString(line, parseAll=True)
            lines.append(pline)

        return self.generate_STS(lines)
        
    def __init_parser(self):

        varname = Word(alphas+nums+T_US+T_MIN+T_DOT)(P_VARNAME)
        sname = Word(alphas+nums+T_I+T_S+T_US)(P_SNAME)
        boolvalue = Literal(T_TRUE) | Literal(T_FALSE)
        
        ivalue = Word(nums)
        hexvalue = Word(nums + T_A + T_B + T_C + T_D + T_E + T_F)
        bvvalue = Combine(ivalue + T_US + ivalue)
        
        value = (bvvalue | hexvalue)(P_VALUE)

        comment = (T_COM + restOfLine + LineEnd())(P_COMMENT)
        emptyline = (ZeroOrMore(White(' \t')) + LineEnd())(P_EMPTY)

        init = (Literal(T_I)(P_TYPE) + Literal(T_CL) + varname + Literal(T_EQ) + value)(P_INIT)
        inits = OneOrMore(init)

        state = (Literal(T_S)(P_TYPE) + ((varname)(P_ID)) + Literal(T_CL) + ((varname + Literal(T_EQ) + value) | (boolvalue)(P_VALUE)))(P_STATE)
        states = OneOrMore(state)

        trans = (sname(P_START) + Literal(T_ARROW) + sname(P_END) + restOfLine)(P_TRANS)
        transs = OneOrMore(trans)
        
        
        ets = OneOrMore(comment | inits | states | transs | emptyline)


        return ets


    def generate_STS(self, lines):
        init = TRUE()
        trans = TRUE()
        invar = TRUE()

        states = {}
        assigns = set([])
        
        for line in lines:
            if line.comment:
                continue
            if line.init:
                (value, width) = self.__get_bv_value(line.init.value)
                ivar = Symbol(line.init.varname, _BVType(width))

                if T_I not in states:
                    states[T_I] = TRUE()

                states[T_I] = And(states[T_I], EqualsOrIff(ivar, BV(value, width)))
                init = And(init, EqualsOrIff(ivar, BV(value, width)))
                
            if line.state:
                state = TRUE()
                sname = T_S + line.state.id
                if line.state.value != T_TRUE:
                    (value, width) = self.__get_bv_value(line.state.value)
                    ivar = Symbol(line.state.varname, _BVType(width))
                    state = EqualsOrIff(ivar, BV(value, width))

                    assval = (sname, line.state.varname)
                    if assval not in assigns:
                        assigns.add(assval)
                    else:
                        Logger.error("Double assignment for variable \"%s\" at state \"%s\""%(line.state.varname, sname))
                    
                if sname not in states:
                    states[sname] = TRUE()

                states[sname] = And(states[sname], state)
                
        stateid_width = math.ceil(math.log(len(states))/math.log(2))
        stateid_var = Symbol(STATE_ID, _BVType(stateid_width))

        init = And(init, EqualsOrIff(stateid_var, BV(0, stateid_width)))
        invar = And(invar, Implies(EqualsOrIff(stateid_var, BV(0, stateid_width)), states[T_I]))
        states[T_I] = EqualsOrIff(stateid_var, BV(0, stateid_width))
        
        count = 1
        for state in states:
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

        vars_ = [v for v in trans.get_free_variables() if not TS.is_prime(v)]
        vars_ += init.get_free_variables()
        vars_ += invar.get_free_variables()
        ts = TS(set(vars_), init, trans, invar)
        ts.comment = "Additional system"

        return ts
                
    def __get_bv_value(self, value):
        if T_US in value:
            width = int(value.split(T_US)[1])
            value = int(value.split(T_US)[0])
        else:
            width = len(value)*4
            value = int(("0x%s"%value).lower(), 0)

        return (value, width)
            
