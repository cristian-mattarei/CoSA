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
import math
from six.moves import cStringIO

from pysmt.shortcuts import BV, And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify, BVAdd, BVUGE
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.rewritings import conjunctive_partition
from pysmt.typing import BOOL, _BVType

from cosa.util.logger import Logger
from cosa.transition_system import TS, HTS
from cosa.encoders.coreir import CoreIRParser, SEP

from cosa.printers import TextTracePrinter, VCDTracePrinter, HIDDEN
from cosa.analyzers.bmc import BMC, BMCConfig, FWD
from cosa.problem import VerificationStatus
from cosa.util.formula_mngm import substitute, get_free_variables

NL = "\n"

KLIVE_COUNT = HIDDEN+"klive_id%s"+HIDDEN
EQVAR = HIDDEN+"eq_var"+HIDDEN
HEQVAR = HIDDEN+"heq_var"+HIDDEN

class BMCLiveness(BMC):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0

    def __init__(self, hts, config):
        BMC.__init__(self, hts, config)

    def solve_liveness(self, hts, prop, k, k_min=0, eventually=False, lemmas=None):
        if lemmas is not None:
            (hts, res) = self.add_lemmas(hts, prop, lemmas)
            if res:
                Logger.log("Lemmas imply the property", 1)
                Logger.log("", 0, not(Logger.level(1)))
                return (0, True)
        
        if self.config.incremental:
            return self.solve_liveness_inc(hts, prop, k, k_min, eventually)

        return self.solve_liveness_fwd(hts, prop, k)
            
    def solve_liveness_inc(self, hts, prop, k, k_min, eventually=False):
        if self.config.strategy == FWD:
            return self.solve_liveness_inc_fwd(hts, prop, k, k_min, eventually)

        Logger.error("Invalid configuration strategy")
        
        return None

    def _compile_counter(self, prop, k):
        if k <= 1:
            counter_width = 1
        else:
            counter_width = math.ceil(math.log(k)/math.log(2))

        idcounter = 0
        while True:
            try:
                counter_var = Symbol((KLIVE_COUNT)%(idcounter), _BVType(counter_width))
                break
            except:
                idcounter +=1
        
        one = BV(1, counter_width)
        zero = BV(0, counter_width)
        
        init = EqualsOrIff(counter_var, BV(0, counter_width))
        count1 = Implies(Not(prop), EqualsOrIff(TS.get_prime(counter_var), BVAdd(counter_var, one)))
        count0 = Implies(prop, EqualsOrIff(TS.get_prime(counter_var), zero))
        trans = And(count0, count1)

        return (counter_var, init, trans)

    def _klive_property(self, counter_var, t):
        klive_prop = BVUGE(counter_var, BV(t, counter_var.symbol_type().width))
        return self.at_time(klive_prop, t)
    
    def solve_liveness_inc_fwd(self, hts, prop, k, k_min, eventually=False):
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
                Logger.get_timer(timer)

        heqvar = None
        if not eventually:
            heqvar = Symbol(HEQVAR, BOOL)
            self._init_at_time(hts.vars.union(set([heqvar])), k)

        if self.config.prove:
            self._reset_assertions(self.solver_2)
            self._add_assertion(self.solver_2, self.at_time(invar, 0))

            if eventually:
                self._add_assertion(self.solver_2, self.at_time(init, 0))
        
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
                loopback = self.all_loopbacks(self.hts.vars, t, heqvar)
                
            Logger.log("Add loopbacks at time %d"%t, 2)
            self._add_assertion(self.solver, loopback)

            if t >= k_min:
                self._write_smt2_comment(self.solver, "Solving for k=%s"%(t))
                Logger.log("\nSolving for k=%s"%(t), 1)
                res = self._solve(self.solver)

                if res:
                    Logger.log("Counterexample found with k=%s"%(t), 1)
                    model = self.solver.solver.get_model()
                    Logger.log("", 0, not(Logger.level(1)))
                    return (t, model)
                else:
                    Logger.log("No counterexample found with k=%s"%(t), 1)
                    Logger.msg(".", 0, not(Logger.level(1)))
            else:
                Logger.log("Skipping solving for k=%s (k_min=%s)"%(t,k_min), 1)
                Logger.msg(".", 0, not(Logger.level(1)))
                    
            self._pop(self.solver)

            n_prop = Not(prop)
            if not eventually:
                n_prop = Or(n_prop, Not(heqvar))
            
            if next_prop:
                if t > 0:
                    propt = self.at_time(n_prop, t-1)
            else:
                propt = self.at_time(n_prop, t)
                
            self._add_assertion(self.solver, propt)

            if self.config.prove:
                
                if t > 0:
                    self._add_assertion(self.solver_2, trans_t)
                    self._write_smt2_comment(self.solver_2, "Solving for k=%s"%(t))

                    if next_prop:
                        if t > 0:
                            propt = self.at_time(Not(prop), t-1)
                    else:
                        propt = self.at_time(Not(prop), t)
                    
                    self._add_assertion(self.solver_2, propt)


                    if t >= k_min:

                        res = self._solve(self.solver_2)

                        if res:
                            Logger.log("K-Liveness failed with k=%s"%(t), 1)
                        else:
                            Logger.log("K-Liveness holds with k=%s"%(t), 1)
                            Logger.log("", 0, not(Logger.level(1)))
                            return (t, True)

                else:
                    self._push(self.solver_2)
                    self._add_assertion(self.solver_2, self.at_time(prop, 0))
                    res = self._solve(self.solver_2)
                    self._pop(self.solver_2)
                    if res:
                        self._add_assertion(self.solver_2, self.at_time(prop, 0))
                    else:
                        self._add_assertion(self.solver_2, self.at_time(Not(prop), 0))
                        
            trans_t = self.unroll(trans, invar, t+1, t)
            self._add_assertion(self.solver, trans_t)
            
            if self.assert_property:
                prop_t = self.unroll(TRUE(), prop, t, t-1)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)
                
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)

    def all_loopbacks(self, vars, k, heqvar=None):
        lvars = list(vars)
        vars_k = [TS.get_timed(v, k) for v in lvars]
        loopback = FALSE()
        eqvar = None
        heqvars = None

        if heqvar is not None:
            eqvar = Symbol(EQVAR, BOOL)
            heqvars = []

        peqvars = FALSE()
            
        for i in range(k):
            vars_i = [TS.get_timed(v, i) for v in lvars]
            eq_k_i = And([EqualsOrIff(vars_k[j], vars_i[j]) for j in range(len(lvars))])
            if heqvar is not None:
                eqvar_i = TS.get_timed(eqvar, i)
                peqvars = Or(peqvars, eqvar_i)
                eq_k_i = And(eqvar_i, Iff(eqvar_i, eq_k_i))

                heqvars.append(Iff(TS.get_timed(heqvar, i), peqvars))
                
            loopback = Or(loopback, eq_k_i)

        if heqvar is not None:
            loopback = And(loopback, And(heqvars))
            
        return loopback
    
    def liveness(self, prop, k, k_min, lemmas=None):
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_liveness(self.hts, prop, k, k_min, False, lemmas)

        model = self._remap_model(self.hts.vars, model, t)

        if model == True:
            return (VerificationStatus.TRUE, None)
        elif t > -1:
            trace = self.print_trace(self.hts, model, t, get_free_variables(prop), map_function=self.config.map_function, find_loop=True)
            return (VerificationStatus.FALSE, trace)
        else:
            return (VerificationStatus.UNK, None)

    def eventually(self, prop, k, k_min, lemmas=None):
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_liveness(self.hts, prop, k, k_min, True, lemmas)

        model = self._remap_model(self.hts.vars, model, t)

        if model == True:
            return (VerificationStatus.TRUE, None)
        elif t > -1:
            trace = self.print_trace(self.hts, model, t, get_free_variables(prop), map_function=self.config.map_function, find_loop=True)
            return (VerificationStatus.FALSE, trace)
        else:
            return (VerificationStatus.UNK, None)
        
