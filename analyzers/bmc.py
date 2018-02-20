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
from core.transition_system import TS, HTS

from util.logger import Logger

class BMC(object):

    hts = None
    prop = None
    
    def __init__(self, hts):
        self.hts = hts
        self.prop = None

        self.solver = Solver(name="z3")


    def set_property(self, prop):
        self.prop = prop

    def at_time(self, trans, i):
        varmap_i  = [(v, TS.get_timed(v, i)) for v in self.hts.vars]
        varmap_ip = [(TS.get_prime(v), TS.get_timed(v, i+1)) for v in self.hts.vars]

        varmap = dict(varmap_i + varmap_ip)

        return trans.substitute(varmap)
        
    def unroll(self, k):
        self.hts.remove_invars()
        init = self.hts.single_init()
        trans = self.hts.single_trans()

        formula = init

        for i in range(k):
            formula = And(formula, self.at_time(trans, i))

        return formula
        
        
    def simulate(self, k):
        formula = self.unroll(k)

        self.solver.reset_assertions()
        self.solver.add_assertion(formula)
        res = self.solver.solve()

        if res:
            Logger.log("SAT", 0)

    
