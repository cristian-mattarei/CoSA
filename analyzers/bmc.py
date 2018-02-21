# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import And, Solver
from core.transition_system import TS, HTS, SEP

from util.logger import Logger

NSEP = "."

class BMC(object):

    hts = None
    prop = None
    
    def __init__(self, hts):
        self.hts = hts
        self.prop = None

        self.solver = Solver(name="z3")


    def set_property(self, prop):
        self.prop = prop

    def at_time(self, trans, t):
        varmap_t  = [(v, TS.get_timed(v, t)) for v in self.hts.vars]
        varmap_tp = [(TS.get_prime(v), TS.get_timed(v, t+1)) for v in self.hts.vars]

        varmap = dict(varmap_t + varmap_tp)

        return trans.substitute(varmap)
        
    def unroll(self, k):
        init = self.hts.single_init()
        trans = self.hts.single_trans()
        invar = self.hts.single_invar()

        formula = And(init, invar)
        formula = self.at_time(formula, 0)
        
        for t in range(k):
            formula = And(formula, self.at_time(trans, t))
            formula = And(formula, self.at_time(trans, t+1))

        return formula

    def remap_name(self, name):
        return name.replace(SEP, NSEP)

    def print_model(self, model, length, only_changing_vars=True):

        Logger.log("---> INIT <---", 0)

        prevass = []
        
        for var in self.hts.vars:
            varass = (var.symbol_name(), model.get_value(TS.get_timed(var, 0)))
            prevass.append(varass)
            Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)

        prevass = dict(prevass)
            
        for t in range(length-1):
            Logger.log("\n---> TIME %s <---"%(t+1), 0)

            for var in self.hts.vars:
                varass = (var.symbol_name(), model.get_value(TS.get_timed(var, t+1)))
                if prevass[varass[0]] != varass[1]:
                    Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)
                    prevass[varass[0]] = varass[1]
                    
        
    def simulate(self, k):
        formula = self.unroll(k)

        self.solver.reset_assertions()
        self.solver.add_assertion(formula)
        res = self.solver.solve()

        if res:
            Logger.log("SAT", 0)
            model = self.solver.get_model()
            self.print_model(model, k)
        else:
            Logger.log("UNSAT", 0)
    
