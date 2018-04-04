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

from pysmt.shortcuts import And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, get_free_variables, simplify
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.rewritings import conjunctive_partition
from pysmt.walkers.identitydag import IdentityDagWalker

from cosa.util.logger import Logger
from cosa.core.transition_system import TS, HTS
from cosa.encoders.coreir import CoreIRParser, SEP

from cosa.printers import TextTracePrinter, VCDTracePrinter
from cosa.analyzers.bmc import BMC, BMCConfig, SubstituteWalker, FWD

import copy

NL = "\n"
            
class BMCLiveness(BMC):

    hts = None
    config = None

    TraceID = 0

    smtvars = None
    total_time = 0.0

    def __init__(self, hts, config):
        self.hts = hts
        self.config = config

        self.assert_property = False
        
        Logger.time = True
        self.total_time = 0.0

        if self.config.smt2file:
            self.smtvars = set([])
            with open(self.config.smt2file, "w") as f:
                f.write("(set-logic QF_BV)\n")

        self.solver = (Solver(name=config.solver_name), "")
        self.subwalker = SubstituteWalker(invalidate_memoization=True)
        
        # BMC.__init__(self, hts, config)

    def solve_liveness(self, hts, prop, k, k_min=0):
        if self.config.incremental:
            return self.solve_liveness_inc(hts, prop, k, k_min)

        return self.solve_liveness_fwd(hts, prop, k)
            
    def solve_liveness_inc(self, hts, prop, k, k_min):
        if self.config.strategy == FWD:
            return self.solve_liveness_inc_fwd(hts, prop, k, k_min)

        Logger.error("Invalid configuration strategy")
        
        return None
        
    def solve_liveness_inc_fwd(self, hts, prop, k, k_min):
        self._reset_assertions(self.solver)

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        if self.config.simplify:
            Logger.log("Simplifying the Transition System", 1)
            if Logger.level(1):
                timer = Logger.start_timer("Simplify")

            init = simplify(init)
            trans = simplify(trans)
            invar = simplify(invar)

            if Logger.level(1):
                Logger.stop_timer(timer)

        propt = FALSE()
        formula = And(init, invar)
        formula = self.at_time(formula, 0)
        Logger.log("Add init and invar", 2)
        self._add_assertion(self.solver, formula)

        next_prop = TS.has_next(prop)
        if next_prop:
            if k < 1:
                Logger.error("Liveness checking with next variables requires at least k=1")
            k_min = 1
        
        t = 0 
        while (t < k+1):
            self._push(self.solver)

            loopback = FALSE()
            if t > 0:
                loopback = self.all_loopback(self.hts.vars, t)
                
            Logger.log("Add loopbacks at time %d"%t, 2)
            self._add_assertion(self.solver, loopback)

            if t >= k_min:
                Logger.log("Solving for k=%s"%(t), 1)

                res = self._solve(self.solver)

                if res:
                    Logger.log("Counterexample found with k=%s"%(t), 1)
                    model = self.solver[0].get_model()
                    Logger.log("", 0, not(Logger.level(1)))
                    return (t, model)
                else:
                    Logger.log("No counterexample found with k=%s"%(t), 1)
                    Logger.msg(".", 0, not(Logger.level(1)))
            else:
                Logger.log("Skipping solving for k=%s (k_min=%s)"%(t,k_min), 1)
                Logger.msg(".", 0, not(Logger.level(1)))
                    
            self._pop(self.solver)

            if next_prop:
                if t > 0:
                    propt = self.at_time(Not(prop), t-1)
            else:
                propt = self.at_time(Not(prop), t)
                
            self._add_assertion(self.solver, propt)
                    
            trans_t = self.unroll(trans, invar, t+1, t)
            self._add_assertion(self.solver, trans_t)
            
            if self.assert_property:
                prop_t = self.unroll(TRUE(), prop, t, t-1)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)
                
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)

    def all_loopback(self, vars, k):
        vars_k = [TS.get_timed(v, k) for v in vars]
        loopback = FALSE()
        
        for i in range(k):
            vars_i = [TS.get_timed(v, i) for v in vars]
            eq_k_i = And([EqualsOrIff(v, vars_i[vars_k.index(v)]) for v in vars_k])
            loopback = Or(loopback, eq_k_i)

        return loopback
    
    def liveness(self, prop, k, k_min):
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_liveness(self.hts, prop, k, k_min)

        model = self._remap_model(self.hts.vars, model, t)
        
        if t > -1:
            Logger.log("Property is FALSE", 0)
            self.print_trace(self.hts, model, t, prop.get_free_variables(), map_function=self.config.map_function)
            return False
        else:
            Logger.log("No counterexample found", 0)
            return True

    def print_trace(self, hts, model, length, xvars=None, diff_only=True, map_function=None):
        trace = []
        prevass = []

        full_trace = self.config.full_trace
        
        if Logger.level(1):
            diff_only = False
            full_trace = True
        
        if self.config.prefix is None:
            printer = TextTracePrinter()
            printer.extra_vars = xvars
            printer.diff_only = diff_only
            printer.full_trace = full_trace
            trace = printer.print_trace(hts, model, length, map_function, True)
            
            Logger.log(trace, 0)
        else:
            if Logger.level(1):
                timer = Logger.start_timer("Trace generation")

            printer = VCDTracePrinter()
            trace = printer.print_trace(hts, model, length, map_function)

            if Logger.level(1):
                Logger.stop_timer(timer)
            
            BMC.TraceID += 1
            trace_file = "%s-id_%s%s"%(self.config.prefix, BMC.TraceID, printer.get_file_ext())
            with open(trace_file, "w") as f:
                f.write(trace)
        
