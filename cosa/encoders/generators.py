# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import math

from pysmt.shortcuts import And, Or, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, \
    BV, BVAdd, BVSub, get_type, BVULT, BVUGT, BVULE
from pysmt.typing import BOOL, BVType, ArrayType
from pysmt.fnode import FNode

from cosa.encoders.template import STSGenerator
from cosa.representation import TS
from cosa.utils.logger import Logger
from cosa.encoders.formulae import StringParser
from cosa.utils.formula_mngm import BV2B

class FixedScoreBoardGenerator(STSGenerator):
    name = "FixedScoreboard"
    description = "Scoreboard for a fifo with no pop"
    interface = "input_port, max_value, push_signal"
    values = "end, tracking"

    def get_param_length(self):
        return 3
    
    def compile_sts(self, name, params):
        in_port, max_val, clk = list(params)

        sb = ScoreBoardGenerator()
        return sb.compile_sts(name, [in_port, max_val, clk, FALSE()])

class ScoreBoardGenerator(STSGenerator):
    name = "Scoreboard"
    description = "Scoreboard for a fifo with push and pop"
    interface = "input_port, max_value, push_signal, pop_signal"
    values = "end, tracking"

    def get_param_length(self):
        return 4

    def compile_sts(self, name, params):
        sparser = StringParser()
        in_port, max_val, c_push, c_pop = list(params)
        max_val = int(max_val)

        if type(c_push) == str:
            c_push = sparser.parse_formula(c_push)
        if type(c_pop) == str:
            c_pop = sparser.parse_formula(c_pop)

        tracking = Symbol("%s.tracking"%name, BOOL)
        end = Symbol("%s.end"%name, BOOL)
        done = Symbol("%s.done"%name, BOOL)
        packet = Symbol("%s.packet"%name, BVType(in_port.symbol_type().width))
        max_width = math.ceil(math.log(max_val)/math.log(2))

        max_bvval = BV(max_val, max_width)
        zero = BV(0, max_width)
        one = BV(1, max_width)
        count = Symbol("%s.count"%name, BVType(max_width))
        size = Symbol("%s.size"%name, BVType(max_width))
        
        pos_c_push = BV2B(c_push)
        neg_c_push = Not(BV2B(c_push))

        pos_c_pop = BV2B(c_pop)
        neg_c_pop = Not(BV2B(c_pop))

        init = []
        trans = []
        invar = []
        
        # INIT DEFINITION #

        # count = 0
        init.append(EqualsOrIff(count, BV(0, max_width)))
        # tracking = False
        init.append(EqualsOrIff(tracking, FALSE()))
        # size = 0
        init.append(EqualsOrIff(size, BV(0, max_width)))
        # end = false
        init.append(EqualsOrIff(end, FALSE()))

        # INVAR DEFINITION #

        # !done -> (end = (tracking & (size = count)))
        invar.append(Implies(Not(done), EqualsOrIff(end, And(tracking, EqualsOrIff(size, count)))))
        
        # count <= size
        invar.append(BVULE(count, size))
        # count <= maxval
        invar.append(BVULE(count, max_bvval))
        # size <= maxval
        invar.append(BVULE(size, max_bvval))

        # done -> (end <-> False);
        invar.append(Implies(done, EqualsOrIff(end, FALSE())))
        # done -> (count = 0_8);
        invar.append(Implies(done, EqualsOrIff(count, BV(0, max_width))))
        # done -> (size = 0_8);
        invar.append(Implies(done, EqualsOrIff(size, BV(0, max_width))))
        # done -> (packet = 0_8);
        invar.append(Implies(done, EqualsOrIff(packet, BV(0, in_port.symbol_type().width))))
        
        # TRANS DEFINITION #

        # (!end & !done) -> next(!done);
        trans.append(Implies(And(Not(end), Not(done)), TS.to_next(Not(done))))
        # end -> next(done);
        trans.append(Implies(end, TS.to_next(done)))
        # done -> next(done);
        trans.append(Implies(done, TS.to_next(done)))
        
        # tracking -> next(tracking);
        trans.append(Implies(Not(done), Implies(tracking, TS.to_next(tracking))))
        # tracking -> (next(packet) = packet);
        trans.append(Implies(Not(done), Implies(tracking, EqualsOrIff(TS.to_next(packet), packet))))
        # !tracking & next(tracking) -> c_push;
        trans.append(Implies(Not(done), Implies(And(Not(tracking), TS.to_next(tracking)), pos_c_push)))
        # (c_push & next(tracking)) -> ((packet = in) & (next(packet) = in);
        trans.append(Implies(Not(done), Implies(And(pos_c_push, TS.to_next(tracking)), And(EqualsOrIff(packet, in_port), EqualsOrIff(TS.to_next(packet), in_port)))))
        # (c_push & !c_pop & tracking) -> (next(count) = (count + 1_8));
        trans.append(Implies(Not(done), Implies(And(pos_c_push, neg_c_pop, tracking), EqualsOrIff(TS.to_next(count), BVAdd(count, BV(1, max_width))))))
        # (c_push & size < maxval) -> (next(size) = (size + 1_8));
        trans.append(Implies(Not(done), Implies(And(pos_c_push, BVULT(size, max_bvval)), EqualsOrIff(TS.to_next(size), BVAdd(size, BV(1, max_width))))))
        # (c_pop & size > 0) -> (next(size) = (size - 1_8));
        trans.append(Implies(Not(done), Implies(And(pos_c_pop, BVUGT(size, zero)), EqualsOrIff(TS.to_next(size), BVSub(size, BV(1, max_width))))))
        # (!(c_push | c_pop)) -> (next(count) = count);
        trans.append(Implies(Not(done), Implies(Not(Or(pos_c_push, pos_c_pop)), EqualsOrIff(count, TS.to_next(count)))))
        # ((c_push | c_pop) & !tracking) -> (next(count) = count);
        trans.append(Implies(Not(done), Implies(And(Or(pos_c_push, pos_c_pop), Not(tracking)), EqualsOrIff(count, TS.to_next(count)))))

        # (c_push & size = maxval) -> (next(size) = size);
        trans.append(Implies(Not(done), Implies(And(pos_c_push, EqualsOrIff(size, max_bvval)), EqualsOrIff(TS.to_next(size), size))))
        # (!(c_push | c_pop)) -> (next(size) = size);
        trans.append(Implies(Not(done), Implies(Not(Or(pos_c_push, pos_c_pop)), EqualsOrIff(size, TS.to_next(size)))))
        # (!(c_push | c_pop)) -> (next(count) = count);
        trans.append(Implies(Not(done), Implies(Not(Or(pos_c_push, pos_c_pop)), EqualsOrIff(count, TS.to_next(count)))))
        # (c_pop & size = 0) -> (next(size) = 0);
        trans.append(Implies(Not(done), Implies(And(pos_c_pop, EqualsOrIff(size, zero)), EqualsOrIff(TS.to_next(size), zero))))

        # (!c_push) -> (next(count) = count);
        trans.append(Implies(Not(done), Implies(neg_c_push, EqualsOrIff(TS.to_next(count), count))))
        
        init = And(init)
        invar = And(invar)
        trans = And(trans)

        ts = TS()
        ts.vars, ts.init, ts.invar, ts.trans = set([tracking, end, packet, count, size]), init, invar, trans

        return ts
    
class RandomGenerator(STSGenerator):
    name = "Random"
    description = "Random Generator"
    interface = "varsize"
    values = "value"

    def get_param_length(self):
        return 1
    
    def compile_sts(self, name, params):
        ts = TS()
        parsize = params[0]
        size = None
        
        if type(parsize) == str:
            sparser = StringParser()
            parsize = sparser.parse_formula(parsize)

        if parsize.is_constant():
            size = parsize.constant_value()

        if get_type(parsize).is_bv_type():
            size = get_type(parsize).width
            
        if size is None:
            Logger.error("Undefined size for symbol \"%s\""%(params[0]))

        value = Symbol("%s.value"%name, BVType(size))
        ts.add_var(value)
        ts.trans = EqualsOrIff(value, TS.get_prime(value))

        return ts
    
