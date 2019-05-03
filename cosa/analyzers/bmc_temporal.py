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

from pysmt.shortcuts import BV, And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify, BVAdd, BVUGE
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.typing import BOOL

from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.representation import TS, HTS
from cosa.encoders.coreir import CoreIRParser, SEP

from cosa.printers.template import HIDDEN_VAR
from cosa.analyzers.mcsolver import VerificationStrategy
from cosa.problem import VerificationStatus

from cosa.analyzers.mcsolver import TraceSolver, BMCSolver

NL = "\n"

EQVAR = HIDDEN_VAR+"eq_var"+HIDDEN_VAR[::-1]
HEQVAR = HIDDEN_VAR+"heq_var"+HIDDEN_VAR[::-1]

class BMCTemporal(BMCSolver):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0

    def __init__(self, hts, config):
        BMCSolver.__init__(self, hts, config)

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
        if self.config.strategy in [VerificationStrategy.FWD, VerificationStrategy.AUTO]:
            return self.solve_liveness_inc_fwd(hts, prop, k, k_min, eventually)

        Logger.error("Invalid configuration strategy")
        
        return None

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
            self.solver_klive = self.solver.copy("klive")
            
            self._reset_assertions(self.solver_klive)
            self._add_assertion(self.solver_klive, self.at_time(invar, 0))

            if eventually:
                self._add_assertion(self.solver_klive, self.at_time(init, 0))
        
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
                
                if self._solve(self.solver):
                    Logger.log("Counterexample found with k=%s"%(t), 1)
                    model = self._get_model(self.solver)
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
                    self._add_assertion(self.solver_klive, trans_t)
                    self._write_smt2_comment(self.solver_klive, "Solving for k=%s"%(t))

                    if next_prop:
                        if t > 0:
                            propt = self.at_time(Not(prop), t-1)
                    else:
                        propt = self.at_time(Not(prop), t)
                    
                    self._add_assertion(self.solver_klive, propt)


                    if t >= k_min:
                        if self._solve(self.solver_klive):
                            Logger.log("K-Liveness failed with k=%s"%(t), 1)
                        else:
                            Logger.log("K-Liveness holds with k=%s"%(t), 1)
                            return (t, True)

                else:
                    self._add_assertion(self.solver_klive, self.at_time(Not(prop), 0))

                    # self._push(self.solver_klive)
                    # self._add_assertion(self.solver_klive, self.at_time(prop, 0))
                    # res = self._solve(self.solver_klive)
                    # self._pop(self.solver_klive)
                    # if res:
                    #     self._add_assertion(self.solver_klive, self.at_time(prop, 0))
                    # else:
                    #     self._add_assertion(self.solver_klive, self.at_time(Not(prop), 0))
                        
            trans_t = self.unroll(trans, invar, t+1, t)
            self._add_assertion(self.solver, trans_t)
            
            if self.assert_property:
                prop_t = self.unroll(TRUE(), prop, t, t-1)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)
                
            t += 1
                
        return (t-1, None)

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
    
    def liveness(self, prop, k, k_min):
        lemmas = self.hts.lemmas
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_liveness(self.hts, prop, k, k_min, False, lemmas)

        model = self._remap_model(self.hts.vars, model, t)

        if model == True:
            return (VerificationStatus.TRUE, None, t)
        elif model is not None:
            trace = self.generate_trace(model, t, get_free_variables(prop), find_loop=True)
            return (VerificationStatus.FALSE, trace, t)
        else:
            return (VerificationStatus.UNK, None, t)

    def eventually(self, prop, k, k_min):
        lemmas = self.hts.lemmas
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_liveness(self.hts, prop, k, k_min, True, lemmas)

        model = self._remap_model(self.hts.vars, model, t)

        if model == True:
            return (VerificationStatus.TRUE, None, t)
        elif model is not None:
            trace = self.generate_trace(model, t, get_free_variables(prop), find_loop=True)
            return (VerificationStatus.FALSE, trace, t)
        else:
            return (VerificationStatus.UNK, None, t)
        
