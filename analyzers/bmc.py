# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import And, Solver, TRUE, Not
from pysmt.parsing import HRParser, parse
from core.transition_system import TS, HTS, SEP

from six.moves import cStringIO
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter

from util.logger import Logger
import re

NSEP = "."

KEYWORDS = ["not"]

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
        
    def unroll(self, k, assumption=TRUE()):
        init = self.hts.single_init()
        trans = self.hts.single_trans()
        invar = self.hts.single_invar()

        formula = And(init, invar)
        formula = self.at_time(formula, 0)
        
        for t in range(k+1):
            formula = And(formula, self.at_time(assumption, t))
            formula = And(formula, self.at_time(trans, t))
            formula = And(formula, self.at_time(trans, t+1))
            formula = And(formula, self.at_time(invar, t+1))

        return formula

    def remap_name(self, name):
        return name.replace(SEP, NSEP)

    def print_model(self, model, length, diff_only=True):

        Logger.log("---> INIT <---", 0)

        prevass = []
        
        for var in self.hts.vars:
            varass = (var.symbol_name(), model.get_value(TS.get_timed(var, 0)))
            if diff_only: prevass.append(varass)
            Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)

        if diff_only: prevass = dict(prevass)
            
        for t in range(length):
            Logger.log("\n---> STEP %s <---"%(t+1), 0)

            for var in self.hts.vars:
                varass = (var.symbol_name(), model.get_value(TS.get_timed(var, t+1)))
                if (not diff_only) or (prevass[varass[0]] != varass[1]):
                    Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)
                    if diff_only: prevass[varass[0]] = varass[1]
                    
        
    def simulate(self, k):
        formula = self.unroll(k)
        
        if Logger.level(2):
            buf = cStringIO()
            printer = SmtPrinter(buf)
            printer.printer(formula)
            print(buf.getvalue())
        
        self.solver.reset_assertions()
        self.solver.add_assertion(formula)
        res = self.solver.solve()

        if res:
            Logger.log("TRACE:", 0)
            model = self.solver.get_model()
            self.print_model(model, k)
        else:
            Logger.log("NO TRACE!!", 0)

    def safety(self, strprop, k):
        prop = strprop.replace(".","$")

        for lit in re.findall("([a-zA-Z][a-zA-Z$0-9]*)+", prop):
            if lit in KEYWORDS:
                continue
            prop = prop.replace(lit, "\"%s\""%lit)

        try:
            prop = parse(prop)
        except Exception as e:
            print(e)
            return

        for t in range(k):
            formula = self.unroll(t)
            formula = And(formula, Not(self.at_time(prop, t+1)))

            if Logger.level(2):
                buf = cStringIO()
                printer = SmtPrinter(buf)
                printer.printer(formula)
                print(buf.getvalue())

            self.solver.reset_assertions()
            self.solver.add_assertion(formula)
            res = self.solver.solve()

            if res:
                Logger.log("Property %s is FALSE:"%(strprop), 0)
                model = self.solver.get_model()
                self.print_model(model, t)
                break
            else:
                Logger.log("No counterexample found with k=%s for property \"%s\""%(t+1, strprop), 0)
            
