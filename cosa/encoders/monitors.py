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

from pysmt.shortcuts import And, Or, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, BV, BVAdd
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.representation import TS
from cosa.utils.logger import Logger

class NotRegisteredMonitorException(Exception):
    pass

class MonitorsFactory(object):
    monitors = []

    # Additional monitors should be registered here #
    @staticmethod
    def init_monitors():
        MonitorsFactory.register_monitor(ScoreBoardMonitor())

    @staticmethod
    def register_monitor(monitor):
        if monitor.get_name() not in dict(MonitorsFactory.monitors):
            MonitorsFactory.monitors.append((monitor.get_name(), monitor))

    @staticmethod
    def monitor_by_name(name):
        MonitorsFactory.init_monitors()
        dmonitor = dict(MonitorsFactory.monitors)
        if name not in dmonitor:
            Logger.error("Monitor \"%s\" is not registered"%name)
        return dmonitor[name]

    @staticmethod
    def get_monitors():
        MonitorsFactory.init_monitors()
        return [x[1] for x in MonitorsFactory.monitors]

class STSMonitor(object):
    name = "MONITOR"
    description = "MISSING DESCRIPTION!"
    interface = "MISSING INTERFACE!"

    def __init__(self):
        pass

    def get_sts(self, name, params):
        pass

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def get_interface(self):
        return self.interface
    

class ScoreBoardMonitor(STSMonitor):
    name = "Scoreboard"
    description = "Scoreboard Monitor"
    interface = "input_port, max_value, clock"
    
    def get_sts(self, name, params):
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
