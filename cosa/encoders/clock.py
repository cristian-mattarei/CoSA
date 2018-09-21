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
    BV, BVAdd, BVSub, get_type, BVULT, BVUGT, BVULE, BVUGE, Ite
from pysmt.typing import BOOL, BVType, ArrayType
from pysmt.fnode import FNode

from cosa.encoders.template import ClockBehavior
from cosa.representation import TS
from cosa.utils.logger import Logger
from cosa.encoders.formulae import StringParser
from cosa.utils.formula_mngm import BV2B

CLOCK_COUNTER = "__counter__"

class DeterministicClockBehavior(ClockBehavior):
    name = "DetClock"
    description = "Deterministic alternation of a defined period"
    interface = "clock-var, period"

    def get_default(self, params):
        return self.get_sts([params[0], 1])
    
    def get_sts(self, params):
        if len(params) != len(self.interface.split()):
            Logger.error("Invalid parameters for clock behavior \"%s\""%(self.name))
        clk = params[0]
        cyclestr = params[1]

        try:
            cycle = int(cyclestr)
        except:
            Logger.error("Clock cycle should be an integer number instead of \"%s\""%cyclestr)

        if (not type(clk) == FNode) or (not clk.is_symbol()):
            Logger.error("Clock symbol \"%s\" not found"%(str(clk)))

        init = []
        invar = []
        trans = []
        vars = set([])
        
        if clk.symbol_type().is_bv_type():
            pos_clk = EqualsOrIff(clk, BV(1 ,1))
            neg_clk = EqualsOrIff(clk, BV(0 ,1))
        else:
            pos_clk = clk
            neg_clk = Not(clk)
            
        if cycle < 1:
            Logger.error("Deterministic clock requires at least a cycle of size 1")
            
        if cycle == 1:
            init.append(neg_clk)
            trans.append(Iff(neg_clk, TS.to_next(pos_clk)))

        if cycle > 1:
            statesize = math.ceil(math.log(cycle)/math.log(2))
            counter = Symbol("%s%s"%(clk.symbol_name(), CLOCK_COUNTER), BVType(statesize))
            # 0 counts
            cycle -= 1

            # counter = 0 & clk = 0
            init.append(EqualsOrIff(counter, BV(0, statesize)))
            init.append(neg_clk)

            # counter <= cycle
            invar.append(BVULE(counter, BV(cycle, statesize)))

            # (counter < cycle) -> next(counter) = counter + 1
            trans.append(Implies(BVULT(counter, BV(cycle, statesize)), EqualsOrIff(TS.to_next(counter), BVAdd(counter, BV(1, statesize)))))
            
            # (counter >= cycle) -> next(counter) = 0
            trans.append(Implies(BVUGE(counter, BV(cycle, statesize)), EqualsOrIff(TS.to_next(counter), BV(0, statesize))))

            # (!clk) & (counter < cycle) -> next(!clk)
            trans.append(Implies(And(neg_clk, BVULT(counter, BV(cycle, statesize))), TS.to_next(neg_clk)))
            # (!clk) & (counter >= cycle) -> next(clk)
            trans.append(Implies(And(neg_clk, BVUGE(counter, BV(cycle, statesize))), TS.to_next(pos_clk)))

            # (clk) & (counter < cycle) -> next(clk)
            trans.append(Implies(And(pos_clk, BVULT(counter, BV(cycle, statesize))), TS.to_next(pos_clk)))
            # (clk) & (counter >= cycle) -> next(!clk)
            trans.append(Implies(And(pos_clk, BVUGE(counter, BV(cycle, statesize))), TS.to_next(neg_clk)))

            vars.add(counter)
            
        ts = TS("Clock Behavior")
        ts.vars, ts.init, ts.invar, ts.trans = vars, And(init), And(invar), And(trans)

        Logger.log("Adding clock behavior \"%s(%s)\""%(self.name, ", ".join([str(p) for p in params])), 1)
        
        return ts

class NondeterministicClockBehavior(ClockBehavior):
    name = "NondetClock"
    description = "Nondeterministic alternation of a maximum defined period"
    interface = "clock-var, period"

    def get_default(self, params):
        return self.get_sts([params[0], 3])
    
    def get_sts(self, params):
        if len(params) != len(self.interface.split()):
            Logger.error("Invalid parameters for clock behavior \"%s\""%(self.name))
        clk = params[0]
        cyclestr = params[1]

        try:
            cycle = int(cyclestr)
        except:
            Logger.error("Clock cycle should be an integer number instead of \"%s\""%cyclestr)

        if (not type(clk) == FNode) or (not clk.is_symbol()):
            Logger.error("Clock symbol \"%s\" not found"%(str(clk)))

        init = []
        invar = []
        trans = []
        vars = set([])
        
        if clk.symbol_type().is_bv_type():
            pos_clk = EqualsOrIff(clk, BV(1 ,1))
            neg_clk = EqualsOrIff(clk, BV(0 ,1))
        else:
            pos_clk = clk
            neg_clk = Not(clk)
            
        if cycle < 1:
            Logger.error("Deterministic clock requires at least a cycle of size 1")
            
        if cycle == 1:
            init.append(neg_clk)
            trans.append(Iff(neg_clk, TS.to_next(pos_clk)))

        if cycle > 1:
            statesize = math.ceil(math.log(cycle)/math.log(2))
            counter = Symbol("%s%s"%(clk.symbol_name(), CLOCK_COUNTER), BVType(statesize))
            # 0 counts
            cycle -= 1

            # counter = 0 & clk = 0
            init.append(EqualsOrIff(counter, BV(0, statesize)))
            init.append(neg_clk)

            # counter <= cycle
            invar.append(BVULE(counter, BV(cycle, statesize)))


            # (!clk) & (counter < cycle) -> ((next(!clk) & (next(counter) = counter + 1)) | (next(clk) & (next(counter) = 0)))
            trans.append(Implies(And(neg_clk, BVULE(counter, BV(cycle, statesize))), \
                                 Or(And(TS.to_next(neg_clk), EqualsOrIff(TS.to_next(counter), BVAdd(counter, BV(1, statesize)))), \
                                    And(TS.to_next(pos_clk), EqualsOrIff(TS.to_next(counter), BV(0, statesize))))))

            # (clk) & (counter < cycle) -> ((next(clk) & (next(counter) = counter + 1)) | (next(!clk) & (next(counter) = 0)))
            trans.append(Implies(And(pos_clk, BVULE(counter, BV(cycle, statesize))), \
                                 Or(And(TS.to_next(pos_clk), EqualsOrIff(TS.to_next(counter), BVAdd(counter, BV(1, statesize)))), \
                                    And(TS.to_next(neg_clk), EqualsOrIff(TS.to_next(counter), BV(0, statesize))))))

            # (counter >= cycle) -> ((next(clk) <-> !clk) & (next(counter) = 0))
            trans.append(Implies(BVUGE(counter, BV(cycle, statesize)), And(EqualsOrIff(TS.to_next(pos_clk), neg_clk), EqualsOrIff(TS.to_next(counter), BV(0, statesize)))))

            vars.add(counter)
            
        ts = TS("Clock Behavior")
        ts.vars, ts.init, ts.invar, ts.trans = vars, And(init), And(invar), And(trans)

        Logger.log("Adding clock behavior \"%s(%s)\""%(self.name, ", ".join([str(p) for p in params])), 1)
        
        return ts
    
class ConstantClockBehavior(ClockBehavior):
    name = "ConstClock"
    description = "Constant value"
    interface = "clock-var, value"

    def get_default(self, params):
        return self.get_sts(params)
    
    def get_sts(self, params):
        if len(params) != len(self.interface.split()):
            Logger.error("Invalid parameters for clock behavior \"%s\""%(self.name))
        clk = params[0]
        valuepar = params[1]

        if (not type(clk) == FNode) or (not clk.is_symbol()):
            Logger.error("Clock symbol \"%s\" not found"%(str(clk)))

        if (type(valuepar) == FNode) and (valuepar.is_bv_constant()):
            value = valuepar.constant_value()
        else:            
            try:
                value = int(valuepar)
            except:
                Logger.error("Clock value should be an integer number instead of \"%s\""%valuepar)

        init = []
        invar = []
        trans = []
        vars = set([])

        if clk.symbol_type().is_bv_type():
            pos_clk = EqualsOrIff(clk, BV(1, 1))
            neg_clk = EqualsOrIff(clk, BV(0, 1))
        else:
            pos_clk = clk
            neg_clk = Not(clk)

        if value == 1:
            invar.append(pos_clk)
        else:
            invar.append(neg_clk)
            
        ts = TS("Clock Behavior")
        ts.vars, ts.init, ts.invar, ts.trans = vars, And(init), And(invar), And(trans)

        Logger.log("Adding clock behavior \"%s(%s)\""%(self.name, ", ".join([str(p) for p in params])), 1)
        
        return ts
    
