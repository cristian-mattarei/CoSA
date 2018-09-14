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

class FixedScoreBoardGenerator(STSGenerator):
    name = "FixedScoreboard"
    description = "Scoreboard for a fifo with no pop"
    interface = "input_port, max_value, clock"

    def get_param_length(self):
        return 3
    
    def compile_sts(self, name, params):
        in_port, max_val, clk = list(params)
        max_val = int(max_val)

        zero = BV(0, 1)
        one = BV(1, 1)

        tracking = Symbol("%s.tracking"%name, BOOL)
        end = Symbol("%s.end"%name, BOOL)
        packet = Symbol("%s.packet"%name, BVType(in_port.symbol_type().width))
        max_width = math.ceil(math.log(max_val)/math.log(2))

        max_bvval = BV(max_val, max_width)
        count = Symbol("%s.count"%name, BVType(max_width))
        
        pos_clk = And(EqualsOrIff(clk, zero), EqualsOrIff(TS.to_next(clk), one))
        neg_clk = Not(And(EqualsOrIff(clk, zero), EqualsOrIff(TS.to_next(clk), one)))

        init = []
        init.append(EqualsOrIff(count, BV(0, max_width)))
        init.append(EqualsOrIff(tracking, FALSE()))
        init = And(init)
        
        invar = EqualsOrIff(end, EqualsOrIff(max_bvval, count))

        trans = []
        # tracking -> next(tracking);
        trans.append(Implies(tracking, TS.to_next(tracking)))
        # tracking -> (next(packet) = packet);
        trans.append(Implies(tracking, EqualsOrIff(TS.to_next(packet), packet)))
        # !tracking & next(tracking) -> (next(clk) = 0_1);
        trans.append(Implies(And(Not(tracking), TS.to_next(tracking)), EqualsOrIff(TS.to_next(clk), zero)))
        # ((clk = 0_1) & (next(clk) = 1_1) & next(tracking)) -> (packet = in);
        trans.append(Implies(And(pos_clk, TS.to_next(tracking)), EqualsOrIff(packet, in_port)))
        # ((clk = 0_1) & (next(clk) = 1_1) & tracking) -> (next(count) = (count + 1_8));
        trans.append(Implies(And(pos_clk, tracking), EqualsOrIff(TS.to_next(count), BVAdd(count, BV(1, max_width)))))
        # (!((clk = 0_1) & (next(clk) = 1_1))) -> (next(count) = count);
        trans.append(Implies(neg_clk, EqualsOrIff(count, TS.to_next(count))))
        # ((clk = 0_1) & (next(clk) = 1_1) & !tracking) -> (next(count) = count);
        trans.append(Implies(And(pos_clk, Not(tracking)), EqualsOrIff(count, TS.to_next(count))))

        trans = And(trans)

        ts = TS()
        ts.vars, ts.init, ts.invar, ts.trans = set([tracking, end, packet, count]), init, invar, trans

        return ts

class ScoreBoardGenerator(STSGenerator):
    name = "Scoreboard"
    description = "Scoreboard for a fifo with push and pop"
    interface = "input_port, max_value, signal_push, signal_pop"

    def get_param_length(self):
        return 4
    
    def compile_sts(self, name, params):
        sparser = StringParser()
        in_port, max_val, c_push, c_pop = list(params)
        max_val = int(max_val)

        c_push = sparser.parse_formula(c_push)
        c_pop = sparser.parse_formula(c_pop)
        

        tracking = Symbol("%s.tracking"%name, BOOL)
        end = Symbol("%s.end"%name, BOOL)
        packet = Symbol("%s.packet"%name, BVType(in_port.symbol_type().width))
        max_width = math.ceil(math.log(max_val)/math.log(2))

        max_bvval = BV(max_val, max_width)
        zero = BV(0, max_width)
        one = BV(1, max_width)
        count = Symbol("%s.count"%name, BVType(max_width))
        size = Symbol("%s.size"%name, BVType(max_width))
        
        pos_c_push = c_push
        neg_c_push = Not(c_push)

        pos_c_pop = c_pop
        neg_c_pop = Not(c_pop)
        
        init = []
        trans = []
        invar = []
        
        # Init definition
        
        init.append(EqualsOrIff(count, BV(0, max_width)))
        init.append(EqualsOrIff(tracking, FALSE()))
        init.append(EqualsOrIff(size, BV(0, max_width)))
        init.append(EqualsOrIff(end, FALSE()))

        # Invar definition

        # end = tracking & (size = count)
        invar.append(EqualsOrIff(end, And(tracking, EqualsOrIff(size, count))))

        # count <= size
        invar.append(BVULE(count, size))
        invar.append(BVULE(count, max_bvval))
        invar.append(BVULE(size, max_bvval))
        
        # Trans definition
        
        # tracking -> (!c_push & !c_pop)
        trans.append(Implies(And(Not(tracking), TS.to_next(tracking)), c_push))
        # tracking -> next(tracking);
        trans.append(Implies(tracking, TS.to_next(tracking)))
        # tracking -> (next(packet) = packet);
        trans.append(Implies(tracking, EqualsOrIff(TS.to_next(packet), packet)))
        # !tracking & next(tracking) -> c_push;
        trans.append(Implies(And(Not(tracking), TS.to_next(tracking)), c_push))
        # (c_push & next(tracking)) -> ((packet = in) & (next(packet) = in);
        trans.append(Implies(And(pos_c_push, TS.to_next(tracking)), And(EqualsOrIff(packet, in_port), EqualsOrIff(TS.to_next(packet), in_port))))
        # (c_push & !c_pop & tracking) -> (next(count) = (count + 1_8));
        trans.append(Implies(And(pos_c_push, neg_c_pop, tracking), EqualsOrIff(TS.to_next(count), BVAdd(count, BV(1, max_width)))))
        # (c_push & size < maxval) -> (next(size) = (size + 1_8));
        trans.append(Implies(And(c_push, BVULT(size, max_bvval)), EqualsOrIff(TS.to_next(size), BVAdd(size, BV(1, max_width)))))
        # (c_pop & size > 0) -> (next(size) = (size - 1_8));
        trans.append(Implies(And(c_pop, BVUGT(size, zero)), EqualsOrIff(TS.to_next(size), BVSub(size, BV(1, max_width)))))
        # (!(c_push | c_pop)) -> (next(count) = count);
        trans.append(Implies(Not(Or(pos_c_push, pos_c_pop)), EqualsOrIff(count, TS.to_next(count))))
        # ((c_push | c_pop) & !tracking) -> (next(count) = count);
        trans.append(Implies(And(Or(pos_c_push, pos_c_pop), Not(tracking)), EqualsOrIff(count, TS.to_next(count))))

        # (c_push & size = maxval) -> (next(size) = size);
        trans.append(Implies(And(c_push, EqualsOrIff(size, max_bvval)), EqualsOrIff(TS.to_next(size), size)))
        # (!(c_push | c_pop)) -> (next(size) = size);
        trans.append(Implies(Not(Or(pos_c_push, pos_c_pop)), EqualsOrIff(size, TS.to_next(size))))
        # (c_pop & size = 0) -> (next(size) = 0);
        trans.append(Implies(And(c_pop, EqualsOrIff(size, zero)), EqualsOrIff(TS.to_next(size), zero)))

        # (!c_push) -> (next(count) = count);
        trans.append(Implies(neg_c_push, EqualsOrIff(TS.to_next(count), count)))
        
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

    def get_param_length(self):
        return 1
    
    def compile_sts(self, name, params):
        ts = TS()
        size = None
        if type(params[0]) == str:
            size = int(params[0])

        if type(params[0]) == FNode:
            size = get_type(params[0]).width
            
        assert size is not None

        value = Symbol("%s.value"%name, BVType(size))
        ts.add_var(value)
        ts.trans = EqualsOrIff(value, TS.get_prime(value))

        return ts
    
