# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import re
from six.moves import cStringIO

from pysmt.shortcuts import And, Solver, TRUE, FALSE, Not, EqualsOrIff, Iff, Symbol, BOOL
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter

from cosa.util.logger import Logger
from cosa.core.transition_system import TS, HTS, SEP

NSEP = "."
NL = "\n"

S1 = "sys1$"
S2 = "sys2$"

class BMCConfig(object):

    incremental = False
    solver = None
    full_trace = False
    prefix = None
    
    def __init__(self):
        self.incremental = True
        self.solver = Solver(name="z3")
        self.full_trace = False
        self.prefix = None

class BMC(object):

    hts = None
    config = None

    TraceID = 0

    def __init__(self, hts):
        self.hts = hts
        self.config = BMCConfig()

    def at_time(self, hts, trans, t):
        varmap_t  = [(v, TS.get_timed(v, t)) for v in hts.vars]
        varmap_tp = [(TS.get_prime(v), TS.get_timed(v, t+1)) for v in hts.vars]

        varmap = dict(varmap_t + varmap_tp)

        return trans.substitute(varmap)
        
    def unroll(self, hts, k_end, k_start=0, assumption=TRUE()):
        Logger.log("Unroll from %s to %s"%(k_start, k_end), 2)
        
        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        formula = TRUE()
        
        if k_start == 0:
            formula = And(init, invar)
            formula = self.at_time(hts, formula, 0)
            Logger.log("Add init and invar", 2)
        else:
            if k_start == k_end:
                k_start -= 1
            
        t = k_start
        while t < k_end:
            formula = And(formula, self.at_time(hts, assumption, t))
            formula = And(formula, self.at_time(hts, trans, t))
            formula = And(formula, self.at_time(hts, invar, t+1))
            Logger.log("Add trans, k=%s"%t, 2)
            t += 1

        return formula

    def remap_name(self, name):
        return name.replace(SEP, NSEP)

    def print_trace(self, hts, model, length, diff_only=True):
        trace = []
        prevass = []
            
        trace.append("---> INIT <---")

        if self.config.full_trace:
            varlist = list(hts.vars)
        else:
            varlist = list(hts.inputs.union(hts.outputs).union(hts.state_vars))

        strvarlist = [(var.symbol_name(), var) for var in varlist]
        strvarlist.sort()
        
        for var in varlist:
            varass = (var.symbol_name(), model.get_value(TS.get_timed(var, 0)))
            if diff_only: prevass.append(varass)
            trace.append("  I: %s = %s"%(self.remap_name(varass[0]), varass[1]))

        if diff_only: prevass = dict(prevass)
            
        for t in range(length):
            trace.append("\n---> STATE %s <---"%(t+1))
                     
            for var in strvarlist:
                varass = (var[1].symbol_name(), model.get_value(TS.get_timed(var[1], t+1)))
                if (not diff_only) or (prevass[varass[0]] != varass[1]):
                    trace.append("  S%s: %s = %s"%(t+1, self.remap_name(varass[0]), varass[1]))
                    if diff_only: prevass[varass[0]] = varass[1]

        trace = NL.join(trace)
        if self.config.prefix is None:
            Logger.log(trace, 0)
        else:
            BMC.TraceID += 1
            trace_file = "%s-id_%s.txt"%(self.config.prefix, BMC.TraceID)
            with open(trace_file, "w") as f:
                f.write(trace)

    def equivalence(self, hts2, k, symbolic_init, inc=True):
        (htseq, t, model) = self.combined_system(hts2, k, symbolic_init, inc)
            
        if t > -1:
            Logger.log("Systems are NOT equivalent", 0)
            self.print_trace(htseq, model, t)
        else:
            Logger.log("Systems are equivalent with k=%s"%k, 0)
            

    def fsm_check(self):
        (htseq, t, model) = self.combined_system(self.hts, 1, True, False)
            
        if t > -1:
            Logger.log("FSM is NOT deterministic", 0)            
            self.print_trace(htseq, model, t)
        else:
            Logger.log("FSM is deterministic", 0)
            
                
    def combined_system(self, hts2, k, symbolic_init, inc=True):
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
        ts1.state_vars = set([TS.get_prefix(v, S1) for v in self.hts.state_vars])

        ts2 = TS(set([TS.get_prefix(v, S2) for v in hts2.vars]),\
                 ts2_init,\
                 hts2.single_trans().substitute(map2),\
                 hts2.single_invar().substitute(map2))
        ts2.state_vars = set([TS.get_prefix(v, S2) for v in hts2.state_vars])

        htseq.add_ts(ts1)
        htseq.add_ts(ts2)

        inputs = self.hts.inputs.union(hts2.inputs)
        outputs = self.hts.outputs.union(hts2.outputs)

        htseq.inputs = set([TS.get_prefix(v, S1) for v in self.hts.inputs]).union(set([TS.get_prefix(v, S2) for v in hts2.inputs]))
        htseq.outputs = set([TS.get_prefix(v, S1) for v in self.hts.outputs]).union(set([TS.get_prefix(v, S2) for v in hts2.outputs]))
        
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

        (t, model) = self.solve(htseq, miter_out, k, inc)
            
        return (htseq, t, model)
                    
    def simulate(self, k):
        self.config.incremental = False
        (t, model) = self.solve(self.hts, FALSE(), k, False)
            
        if t > -1:
            self.print_trace(self.hts, model, t)
        else:
            Logger.log("Deadlock wit k=%s"%k, 0)

    def solve(self, hts, prop, k, inc=True):
        if self.config.incremental:
            self.config.solver.reset_assertions()
        
        t = 0 if inc else k
        while (t < k+1):
            if not self.config.incremental:
                self.config.solver.reset_assertions()

            t_start = 0 if not self.config.incremental else t

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
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.config.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            if self.config.incremental:
                self.config.solver.pop()
                
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)

            
    def safety(self, prop, k):
        
        (t, model) = self.solve(self.hts, prop, k)

        if t > -1:
            Logger.log("Property is FALSE", 0)
            self.print_trace(self.hts, model, t)
        else:
            Logger.log("No counterexample found", 0)
