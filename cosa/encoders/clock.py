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
    BV, BVAdd, BVSub, get_type, BVULT, BVUGT, BVULE, BVUGE
from pysmt.typing import BOOL, BVType, ArrayType
from pysmt.fnode import FNode

from cosa.encoders.template import ClockBehavior
from cosa.representation import TS
from cosa.utils.logger import Logger
from cosa.encoders.formulae import StringParser
from cosa.utils.formula_mngm import BV2B

class DeterminisitcClockBehavior(ClockBehavior):
    name = "DetClock"
    description = "Deterministic alternation of cycle k"

    def get_sts(self, clk, params):
        cyclestr = params[0]

        try:
            cycle = int(cyclestr)
        except:
            Logger.error("Clock cycle should be an integer number instead of \"%s\""%cyclestr)

        if (not type(clk) == FNode) and (not clk.is_symbol()):
            Logger.error("Error processing clock signal")

        init = []
        invar = []
        trans = []
            
        if cycle == 1:
            if clk.symbol_type().is_bv_type():
                init.append(EqualsOrIff(clk, BV(0,1)))
                trans.append(Iff(EqualsOrIff(clk, BV(0,1)), EqualsOrIff(TS.to_next(clk), BV(1,1))))
            else:
                init.append(Not(clk))
                trans.append(Iff(Not(clk), TS.to_next(clk)))

        if cycle > 1:
            statesize = math.ceil(math.log(cycle)/math.log(2))
            stateidx = Symbol(clockname, BVType(statesize))
            invar.append(BVULE(stateidx, BV(cycle, statesize)))
            init.append(EqualsOrIff(stateidx, BV(cycle, 0)))

            trans.append(Implies(BVULT(stateidx, BV(cycle, statesize)), EqualsOrIff(TS.get_next(stateidx), BVAdd(stateidx, BV(1, statesize)))))
            trans.append(Implies(BVUGE(stateidx, BV(cycle, statesize)), EqualsOrIff(TS.get_next(stateidx), BV(0, statesize))))
            

        ts = TS("Clock Behavior")
        ts.init, ts.invar, ts.trans = And(init), And(invar), And(trans)
                
        return ts
