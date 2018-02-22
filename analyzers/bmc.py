# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import And, Solver, TRUE, Not, EqualsOrIff, Iff, Symbol, BOOL
from pysmt.parsing import HRParser, parse
from core.transition_system import TS, HTS, SEP

from six.moves import cStringIO
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter

from util.logger import Logger
import re

NSEP = "."

KEYWORDS = ["not"]

S1 = "sys1$"
S2 = "sys2$"

class BMCConfig(object):

    incremental = False
    solver = None
    
    def __init__(self):
        self.incremental = True
        self.solver = Solver(name="z3")

class BMC(object):

    hts = None
    config = None

    def __init__(self, hts):
        self.hts = hts
        self.config = BMCConfig()

    def at_time(self, hts, trans, t):
        varmap_t  = [(v, TS.get_timed(v, t)) for v in hts.vars]
        varmap_tp = [(TS.get_prime(v), TS.get_timed(v, t+1)) for v in hts.vars]

        varmap = dict(varmap_t + varmap_tp)

        return trans.substitute(varmap)
        
    def unroll(self, hts, k_end, k_start=0, assumption=TRUE()):
        Logger.log("Unroll from %s to %s"%(k_start, k_end), 1)
        
        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        formula = TRUE()
        
        if k_start == 0:
            formula = And(init, invar)
            formula = self.at_time(hts, formula, 0)
            Logger.log("Add init and invar", 1)
        else:
            if k_start == k_end:
                k_start -= 1
            
        t = k_start
        while t < k_end:
            formula = And(formula, self.at_time(hts, assumption, t))
            formula = And(formula, self.at_time(hts, trans, t))
            formula = And(formula, self.at_time(hts, invar, t+1))
            Logger.log("Add trans, k=%s"%t, 1)
            t += 1

        return formula

    def remap_name(self, name):
        return name.replace(SEP, NSEP)

    def print_model(self, hts, model, length, diff_only=True):

        Logger.log("---> INIT <---", 0)

        prevass = []

        varlist = list(hts.vars)
        varlist
        
        for var in varlist:
            varass = (var.symbol_name(), model.get_value(TS.get_timed(var, 0)))
            if diff_only: prevass.append(varass)
            Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)

        if diff_only: prevass = dict(prevass)
            
        for t in range(length):
            Logger.log("\n---> STATE %s <---"%(t+1), 0)

            for var in varlist:
                varass = (var.symbol_name(), model.get_value(TS.get_timed(var, t+1)))
                if (not diff_only) or (prevass[varass[0]] != varass[1]):
                    Logger.log("  %s = %s"%(self.remap_name(varass[0]), varass[1]), 0)
                    if diff_only: prevass[varass[0]] = varass[1]
                    

    def equivalence(self, hts2, k, symbolic_init, inc=True):
        htseq = HTS("eq")

        map1 = dict([(v, TS.get_prefix(v, S1)) for v in self.hts.vars])
        map2 = dict([(v, TS.get_prefix(v, S2)) for v in hts2.vars])

        ts1_init = TRUE()
        ts2_init = TRUE()
        
        if not symbolic_init:
            ts1_init = self.hts.single_init().substitute(map1)
            ts2_init = hts2.single_init().substitute(map2)
        
        ts1 = TS(set([TS.get_prefix(v, S1) for v in self.hts.vars]),\
                 ts1_init,\
                 self.hts.single_trans().substitute(map1),\
                 self.hts.single_invar().substitute(map1))

        ts2 = TS(set([TS.get_prefix(v, S2) for v in hts2.vars]),\
                 ts2_init,\
                 hts2.single_trans().substitute(map2),\
                 hts2.single_invar().substitute(map2))

        htseq.add_ts(ts1)
        htseq.add_ts(ts2)

        inputs = self.hts.inputs.union(hts2.inputs)
        outputs = self.hts.outputs.union(hts2.outputs)

        if symbolic_init:
            states = self.hts.state_vars.union(hts2.state_vars)
        else:
            states = []
            
        eqinputs = TRUE()
        eqoutputs = TRUE()
        eqstates = TRUE()
        
        for inp in inputs:
            eqinputs = And(eqinputs, EqualsOrIff(TS.get_prefix(inp, S1), TS.get_prefix(inp, S2)))

        for out in outputs:
            eqoutputs = And(eqoutputs, EqualsOrIff(TS.get_prefix(out, S1), TS.get_prefix(out, S2)))

        for svar in states:
            eqstates = And(eqstates, EqualsOrIff(TS.get_prefix(svar, S1), TS.get_prefix(svar, S2)))
            
        miter_out = Symbol("eq_S1_S2", BOOL)
        eqoutputs = Iff(miter_out, eqoutputs)

        htseq.add_ts(TS(set([miter_out]), TRUE(), TRUE(), And(eqinputs, eqoutputs)))

        if symbolic_init:
            htseq.add_ts(TS(set([]), eqstates, TRUE(), TRUE()))


        (t, model) = self.solve(htseq, miter_out, "eq_S1_S2", k, inc)
            
        if t > -1:
            self.print_model(htseq, model, t)
        
                    
    def simulate(self, k):
        formula = self.unroll(self.hts, k)
        
        if Logger.level(2):
            buf = cStringIO()
            printer = SmtPrinter(buf)
            printer.printer(formula)
            print(buf.getvalue())
        
        self.config.solver.reset_assertions()
        self.config.solver.add_assertion(formula)
        res = self.config.solver.solve()

        if res:
            Logger.log("TRACE:", 0)
            model = self.config.solver.get_model()
            self.print_model(self.hts, model, k)
        else:
            Logger.log("NO TRACE!!", 0)


    def solve(self, hts, prop, strprop, k, inc=True):
        Logger.log("Safety verification for property \"%s\":"%(strprop), 0)

        if self.config.incremental:
            self.config.solver.reset_assertions()
        
        t = 0 if inc else k
        while (t < k+1):
            if not self.config.incremental:
                self.config.solver.reset_assertions()

            t_start = 0

            if self.config.incremental:
                t_start = t

            formula = self.unroll(hts, t, t_start)
            self.config.solver.add_assertion(formula)

            if self.config.incremental:
                self.config.solver.push()
            
            propt = Not(self.at_time(hts, prop, t))
            self.config.solver.add_assertion(propt)

            if Logger.level(2):
                buf = cStringIO()
                printer = SmtPrinter(buf)
                printer.printer(formula)
                print(buf.getvalue())

            res = self.config.solver.solve()

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 0)
                model = self.config.solver.get_model()
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 0)

            if self.config.incremental:
                self.config.solver.pop()
                
            t += 1
                
        return (-1, None)

            
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

        (t, model) = self.solve(self.hts, prop, strprop, k)

        if t > -1:
            self.print_model(self.hts, model, t)
