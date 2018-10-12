# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify
from pysmt.shortcuts import Interpolator
from pysmt.oracles import get_logic

from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.utils.generic import status_bar
from cosa.representation import TS, HTS

from cosa.problem import VerificationStatus
from cosa.analyzers.mcsolver import TraceSolver, BMCSolver, VerificationStrategy

NL = "\n"

class BMCSafety(BMCSolver):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0
    tracefile = None

    preferred = None

    def __init__(self, hts, config):
        BMCSolver.__init__(self, hts, config)

    def loop_free(self, vars_, k_end, k_start=0):
        Logger.log("Simple path from %s to %s"%(k_start, k_end), 2)

        if k_end == k_start:
            return TRUE()

        def not_eq_states(vars1, vars2):
            assert len(vars1) == len(vars2)
            eqvars = []
            for i in range(len(vars1)):
                eqvars.append(EqualsOrIff(vars1[i], vars2[i]))
            return Not(And(eqvars))

        lvars = list(vars_)
        end_vars = [TS.get_timed(v, k_end) for v in lvars]
        
        formula = []
        for t in range(k_start, k_end, 1):
            formula.append(not_eq_states(end_vars, [TS.get_timed(v, t) for v in lvars]))

        return And(formula)

    def set_preferred(self, preferred):
        if self.preferred is None:
            self.preferred = []
        self.preferred.append(preferred)
    
    def simulate(self, prop, k):
        if self.config.strategy == VerificationStrategy.NU:
            self._init_at_time(self.hts.vars, 1)
            (t, model) = self.sim_no_unroll(self.hts, prop, k)
        else:
            self._init_at_time(self.hts.vars, k)
            if prop == TRUE():
                self.config.incremental = False
                (t, model) = self.solve_safety_fwd(self.hts, Not(prop), k, False)
            else:
                (t, model) = self.solve_safety(self.hts, Not(prop), k)

        model = self._remap_model(self.hts.vars, model, t)
        if (t > -1) and (model is not None):
            Logger.log("Execution found", 1)
            trace = self.generate_trace(model, t, get_free_variables(prop))
            return (VerificationStatus.TRUE, trace)
        else:
            Logger.log("Deadlock wit k=%s"%k, 1)
            return (VerificationStatus.FALSE, None)

    def solve_safety(self, hts, prop, k, k_min=0, lemmas=None):
        if lemmas is not None:
            (hts, res) = self.add_lemmas(hts, prop, lemmas)
            if res:
                Logger.log("Lemmas imply the property", 1)
                Logger.log("", 0, not(Logger.level(1)))
                return (0, True)

        hts.reset_formulae()

        if self.config.incremental:
            return self.solve_safety_inc(hts, prop, k, k_min)

        return self.solve_safety_ninc(hts, prop, k)

    def solve_safety_ninc(self, hts, prop, k):
        if self.config.strategy == VerificationStrategy.ALL:
            res = self.solve_safety_fwd(hts, prop, k)
            if res[1] is not None:
                return res
            if self.config.prove:
                res = self.solve_safety_int(hts, prop, k)
                if res[1] is not None:
                    return res
            return res
        
        if self.config.strategy in [VerificationStrategy.FWD, VerificationStrategy.AUTO]:
            return self.solve_safety_fwd(hts, prop, k)

        if self.config.strategy == VerificationStrategy.INT:
            return self.solve_safety_int(hts, prop, k)
        
        Logger.error("Invalid configuration strategy")

        return None
    
    def solve_safety_inc(self, hts, prop, k, k_min):
        if self.config.strategy == VerificationStrategy.ALL:
            res = self.solve_safety_inc_fwd(hts, prop, k, k_min)
            if res[1] is not None:
                return res
            if self.config.prove and not TS.has_next(prop):
                res = self.solve_safety_int(hts, prop, k)
                if res[1] is not None:
                    return res
            res = self.solve_safety_inc_bwd(hts, prop, k)
            if res[1] is not None:
                self.config.strategy == VerificationStrategy.BWD
                return res
            res = self.solve_safety_inc_zz(hts, prop, k)
            self.config.strategy == VerificationStrategy.ZZ
            return res
        
        if self.config.strategy in [VerificationStrategy.FWD, VerificationStrategy.AUTO]:
            return self.solve_safety_inc_fwd(hts, prop, k, k_min)

        if self.config.strategy == VerificationStrategy.BWD:
            return self.solve_safety_inc_bwd(hts, prop, k)

        if self.config.strategy == VerificationStrategy.ZZ:
            return self.solve_safety_inc_zz(hts, prop, k)
            
        # Redirecting strategy selection error
        if self.config.strategy == VerificationStrategy.INT:
            Logger.warning("Interpolation is not available in incremental mode. Switching to not incremental")
            return self.solve_safety_ninc(hts, prop, k)
            
        Logger.error("Invalid configuration strategy")

        return None

    def solve_safety_int(self, hts, prop, k):
        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        if TS.has_next(prop):
            Logger.error("Interpolation does not support properties with next variables")

        map_10 = dict([(TS.get_timed_name(v.symbol_name(), 1), TS.get_timed_name(v.symbol_name(), 0)) for v in hts.vars])
            
        itp = Interpolator(logic=get_logic(trans))
        init = And(init, invar)
        nprop = Not(prop)
        
        t = 0
        while (t < k+1):
            Logger.log("\nSolving for k=%s"%t, 1)
            int_c = 0
            init_0 = self.at_time(init, 0)
            R = init_0

            trans_t = self.unroll(trans, invar, t, gen_list=True)
            trans_tA = And(trans_t[0]) if t > 0 else TRUE()
            trans_tB = And(trans_t[1:]) if t > 0 else TRUE()
            
            while True:
                self._reset_assertions(self.solver)
                Logger.log("Add init and invar", 2)
                self._add_assertion(self.solver, R)

                self._add_assertion(self.solver, And(trans_tA, trans_tB))

                npropt = self.at_time(nprop, t)
                Logger.log("Add property time %d"%t, 2)
                self._add_assertion(self.solver, npropt)

                if self._solve(self.solver):
                    if R == init_0:
                        Logger.log("Counterexample found with k=%s"%(t), 1)
                        model = self._get_model(self.solver)
                        return (t, model)
                    else:
                        Logger.log("No counterexample or proof found with k=%s"%(t), 1)
                        Logger.msg(".", 0, not(Logger.level(1)))
                        break
                else:
                    if len(trans_t) < 2:
                        Logger.log("No counterexample found with k=%s"%(t), 1)
                        Logger.msg(".", 0, not(Logger.level(1)))
                        break

                    Ri = And(itp.sequence_interpolant([And(R, trans_tA), And(trans_tB, npropt)]))
                    Ri = substitute(Ri, map_10)
                    
                    self._reset_assertions(self.solver)
                    self._add_assertion(self.solver, And(Ri, Not(R)))

                    if not self._solve(self.solver):
                        Logger.log("Proof found with k=%s"%(t), 1)
                        return (t, True)
                    else:
                        R = Or(R, Ri)
                        int_c += 1

                    Logger.log("Extending initial states (%s)"%int_c, 1)

            t += 1

        return (t-1, None)
    
    def solve_safety_fwd(self, hts, prop, k, shortest=True):

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        t_start = 0 if shortest else k

        t = 0 if shortest else k
        while (t < k+1):
            self._reset_assertions(self.solver)

            formula = And(init, invar)
            formula = self.at_time(formula, 0)
            Logger.log("Add init and invar", 2)
            self._add_assertion(self.solver, formula)

            trans_t = self.unroll(trans, invar, t)
            self._add_assertion(self.solver, trans_t)

            propt = self.at_time(Not(prop), t)
            Logger.log("Add property time %d"%t, 2)
            self._add_assertion(self.solver, propt)

            if self._solve(self.solver):
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self._get_model(self.solver)
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            t += 1

        return (t-1, None)
    
    def _check_lemma(self, hts, lemma, init, trans):

        def check_init():
            self._reset_assertions(self.solver)
            self._add_assertion(self.solver, self.at_time(And(init, Not(lemma)), 0), comment="Init check")
            res = self._solve(self.solver)

            prefix = None
            if self.config.prefix is not None:
                prefix = self.config.prefix+"-ind"

            if res:
                Logger.log("Lemma \"%s\" failed for I -> L"%lemma, 2)
                return False

            Logger.log("Lemma \"%s\" holds for I -> L"%lemma, 2)
            return True

        def check_step():
            self._reset_assertions(self.solver)
            self._add_assertion(self.solver, self.at_time(And(trans, lemma), 0))
            self._add_assertion(self.solver, self.at_time(Not(lemma), 1))

            if self._solve(self.solver):
                Logger.log("Lemma \"%s\" failed for L & T -> L'"%lemma, 2)
                return False

            Logger.log("Lemma \"%s\" holds for L & T -> L'"%lemma, 2)
            return True

        if not check_step():
            return False
        if not check_init():
            return False
                
        return True

    def _suff_lemmas(self, prop, lemmas):
        self._reset_assertions(self.solver)

        self._add_assertion(self.solver, And(And(lemmas), Not(prop)))
        
        if self._solve(self.solver):
            return False

        return True

    def add_lemmas(self, hts, prop, lemmas):
        if len(lemmas) == 0:
            return (hts, False)

        self._reset_assertions(self.solver)

        h_init = hts.single_init()
        h_trans = hts.single_trans()
        
        holding_lemmas = []
        lindex = 1
        nlemmas = len(lemmas)
        tlemmas = 0
        flemmas = 0
        for lemma in lemmas:
            Logger.log("\nChecking Lemma %s/%s"%(lindex,nlemmas), 1)
            invar = hts.single_invar()
            init = And(h_init, invar)
            trans = And(invar, h_trans, TS.to_next(invar))
            if self._check_lemma(hts, lemma, init, trans):
                holding_lemmas.append(lemma)
                hts.add_assumption(lemma)
                hts.reset_formulae()
                
                Logger.log("Lemma %s holds"%(lindex), 1)
                tlemmas += 1
                if self._suff_lemmas(prop, holding_lemmas):
                    return (hts, True)
            else:
                Logger.log("Lemma %s does not hold"%(lindex), 1)
                flemmas += 1
                
            msg = "%s T:%s F:%s U:%s"%(status_bar((float(lindex)/float(nlemmas)), False), tlemmas, flemmas, (nlemmas-lindex))
            Logger.inline(msg, 0, not(Logger.level(1))) 
            lindex += 1
            
        Logger.clear_inline(0, not(Logger.level(1)))
        
        hts.assumptions = And(holding_lemmas)
        return (hts, False)

    def solve_safety_inc_fwd(self, hts, prop, k, k_min, all_vars=False, generalize=None):
        self._reset_assertions(self.solver)

        add_unsat_cons = False

        if self.config.prove:
            self.solver_ind = self.solver.copy("ind")
            self._reset_assertions(self.solver_ind)

            if all_vars:
                relevant_vars = hts.vars
            else:
                relevant_vars = hts.state_vars | hts.input_vars | hts.output_vars

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        acc_init = TRUE()
        acc_prop = TRUE()
        acc_loop_free = TRUE()
        trans_t = TRUE()
        
        if self.config.simplify:
            Logger.log("Simplifying the Transition System", 1)
            if Logger.level(2):
                timer = Logger.start_timer("Simplify")

            init = simplify(init)
            trans = simplify(trans)
            invar = simplify(invar)
            if Logger.level(2):
                Logger.get_timer(timer)

        n_prop_t = FALSE()
        init_0 = self.at_time(And(init, invar), 0)
        Logger.log("Add init and invar", 2)
        self._add_assertion(self.solver, init_0)

        if self.config.prove:
            # add invariants at time 0, but not init
            self._add_assertion(self.solver_ind, self.at_time(invar, 0), "invar")

        next_prop = TS.has_next(prop)
        if next_prop:
            if k < 1:
                Logger.error("Invariant checking with next variables requires at least k=1")
            k_min = 1

        t = 0
        skip_push = False

        constraints = TRUE()
        
        while (t < k+1):
            if not skip_push:
                self._push(self.solver)
                skip_push = False

            t_prop = t-1 if next_prop else t
            
            if k_min > 0:
                if (not next_prop) or (next_prop and t>0):
                    if n_prop_t == FALSE():
                        n_prop_t = self.at_time(Not(prop), t_prop)
                    else:
                        n_prop_t = Or(n_prop_t, self.at_time(Not(prop), t_prop))
            else:
                n_prop_t = self.at_time(Not(prop), t)

            Logger.log("Add not property at time %d"%t, 2)
            self._add_assertion(self.solver, n_prop_t, "Property")

            if constraints != TRUE():
                self._add_assertion(self.solver, self.at_time(constraints, t), "Addditional Constraints")
            
            if t >= k_min:
                Logger.log("\nSolving for k=%s"%(t), 1)

                if self.preferred is not None:
                    try:
                        for (var, val) in self.preferred:
                            for t in range(t+1):
                                self.solver.solver.set_preferred_var(TS.get_timed(var, t), val)
                    except:
                        Logger.warning("Current solver does not support preferred variables")

                if self._solve(self.solver):
                    Logger.log("Counterexample found with k=%s"%(t), 1)
                    model = self._get_model(self.solver)

                    if generalize is not None:
                        constr, res = generalize(model, t)
                        if res:
                            return (t, model)
                        constraints = And(constraints, Not(constr))
                        skip_push = True
                        continue
                    else:
                        return (t, model)
                else:
                    Logger.log("No counterexample found with k=%s"%(t), 1)
                    Logger.msg(".", 0, not(Logger.level(1)))

                    if add_unsat_cons and self.config.prove:
                        self._add_assertion(self.solver, Implies(self.at_time(And(init, invar), 1), self.at_time(Not(prop), t_prop+1)))
                        self._add_assertion(self.solver, Not(n_prop_t))
            else:
                Logger.log("\nSkipping solving for k=%s (k_min=%s)"%(t,k_min), 1)
                Logger.msg("_", 0, not(Logger.level(1)))

            self._pop(self.solver)
            skip_push = False
            
            if self.config.prove:
                if t > k_min:
                    loop_free = self.loop_free(relevant_vars, t, t-1)

                    # Checking I & T & loopFree
                    acc_init = And(acc_init, self.at_time(Not(init), t))
                    acc_loop_free = And(acc_loop_free, loop_free)
                    
                    self._push(self.solver)

                    self._add_assertion(self.solver, acc_init)
                    self._add_assertion(self.solver, acc_loop_free)
                    
                    if self._solve(self.solver):
                        Logger.log("Induction (I & lF) failed with k=%s"%(t), 1)
                    else:
                        Logger.log("Induction (I & lF) holds with k=%s"%(t), 1)
                        return (t, True)

                    self._pop(self.solver)

                    # Checking T & loopFree & !P
                    self._add_assertion(self.solver_ind, trans_t, comment="trans")
                    self._add_assertion(self.solver_ind, loop_free, comment="loop_free")
                    
                    self._push(self.solver_ind)

                    self._add_assertion(self.solver_ind, self.at_time(Not(prop), t_prop))

                    if self._solve(self.solver_ind):
                        Logger.log("Induction (lF & !P) failed with k=%s"%(t), 1)
                    else:
                        Logger.log("Induction (lF & !P) holds with k=%s"%(t), 1)
                        return (t, True)

                    self._pop(self.solver_ind)

                    self._add_assertion(self.solver_ind, self.at_time(prop, t_prop), "prop")
                else:
                    if not next_prop:
                        self._add_assertion(self.solver_ind, self.at_time(prop, t_prop), "prop")

            trans_t = self.unroll(trans, invar, t+1, t)
            self._add_assertion(self.solver, trans_t)
                    
            t += 1
            
        return (t-1, None)

    def solve_safety_inc_bwd(self, hts, prop, k, assert_property=False):
        self._reset_assertions(self.solver)

        if TS.has_next(prop):
            Logger.error("Invariant checking with next variables only supports FWD strategy")

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        formula = self.at_ptime(And(Not(prop), invar), -1)
        Logger.log("Add not property at time %d"%0, 2)
        self._add_assertion(self.solver, formula)

        t = 0
        while (t < k+1):
            self._push(self.solver)

            pinit = self.at_ptime(init, t-1)
            Logger.log("Add init at time %d"%t, 2)
            self._add_assertion(self.solver, pinit)

            if self._solve(self.solver):
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self._get_model(self.solver)
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self._pop(self.solver)

            trans_t = self.unroll(trans, invar, t, t+1)
            self._add_assertion(self.solver, trans_t)

            if assert_property and t > 0:
                prop_t = self.unroll(TRUE(), prop, t-1, t)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)

            t += 1

        return (t-1, None)

    def solve_safety_inc_zz(self, hts, prop, k):
        self._reset_assertions(self.solver)

        if TS.has_next(prop):
            Logger.error("Invariant checking with next variables only supports FWD strategy")

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        initt = self.at_time(And(init, invar), 0)
        Logger.log("Add init at_0", 2)
        self._add_assertion(self.solver, initt)

        propt = self.at_ptime(And(Not(prop), invar), -1)
        Logger.log("Add property pat_%d"%0, 2)
        self._add_assertion(self.solver, propt)

        t = 0
        while (t < k+1):
            self._push(self.solver)
            even = (t % 2) == 0
            th = int(t/2)

            if even:
                eq = And([EqualsOrIff(self.at_time(v, th), self.at_ptime(v, th-1)) for v in hts.vars])
            else:
                eq = And([EqualsOrIff(self.at_time(v, th+1), self.at_ptime(v, th-1)) for v in hts.vars])

            Logger.log("Add equivalence time %d"%t, 2)
            self._add_assertion(self.solver, eq)

            if self._solve(self.solver):
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self._get_model(self.solver)
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self._pop(self.solver)

            if even:
                trans_t = self.unroll(trans, invar, th+1, th)
            else:
                trans_t = self.unroll(trans, invar, th, th+1)

            self._add_assertion(self.solver, trans_t)

            t += 1

        return (t-1, None)

    
    def safety(self, prop, k, k_min):
        lemmas = self.hts.lemmas
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve_safety(self.hts, prop, k, k_min, lemmas)

        if model == True:
            return (VerificationStatus.TRUE, None, t)
        elif model is not None:
            model = self._remap_model(self.hts.vars, model, t)
            trace = self.generate_trace(model, t, get_free_variables(prop))
            return (VerificationStatus.FALSE, trace, t)
        else:
            return (VerificationStatus.UNK, None, t)

    def sim_no_unroll(self, hts, cover, k, all_vars=True, inc=False):
        init = hts.single_init()
        invar = hts.single_invar()
        trans = hts.single_trans()

        init_0 = self.at_time(init, 0)
        invar_0 = self.at_time(invar, 0)
        trans_01 = self.unroll(trans, invar, 1)
        cover_1 = self.at_time(cover, 1)

        full_model = {}
        
        if all_vars:
            relevant_vars = hts.vars
        else:
            relevant_vars = hts.state_vars | hts.input_vars | hts.output_vars
        
        relevant_vars_0 = [TS.get_timed(v, 0) for v in relevant_vars]
        relevant_vars_1 = [TS.get_timed(v, 1) for v in relevant_vars]

        relevant_vars_01 = [(TS.get_timed(v, 0), TS.get_timed(v, 1), v) for v in relevant_vars]
        
        self._reset_assertions(self.solver)
        
        # Picking Initial State
        Logger.log("\nSolving for k=0", 1)
        self._add_assertion(self.solver, And(init_0, invar_0))

        if self._solve(self.solver):
            init_model =  self._get_model(self.solver, relevant_vars_0)
            init_0 = And([EqualsOrIff(v, init_model[v]) for v in relevant_vars_0])

            for v in relevant_vars_0:
                full_model[v] = init_model[v]

            Logger.msg(".", 0, not(Logger.level(1)))
        else:
            return (0, None)

        self._reset_assertions(self.solver)
        
        if inc:
            self._add_assertion(self.solver, trans_01)
            self._add_assertion(self.solver, invar_0)

        init_model = None
        for t in range(1, k + 1):
            Logger.log("\nSolving for k=%s"%(t), 1)

            if not inc:
                self._reset_assertions(self.solver, True)

                formula = And(init_0, invar_0)
                self._add_assertion(self.solver, trans_01)
            else:
                formula = init_0
                self._push(self.solver)
                
            self._add_assertion(self.solver, formula)

            res_step = self._solve(self.solver)

            if res_step:
                Logger.msg(".", 0, not(Logger.level(1)))
                Logger.log("Able to step forward at k=%s"%(t), 2)
                if all_vars:
                    init_model = self._get_model(self.solver)
                else:
                    init_model = self._get_model(self.solver, relevant_vars_1)
                model = init_model
            else:
                Logger.log("System deadlocked at k=%s"%(t), 2)
                return (-1, full_model)

            # Use previous model as initial state for next sat call
            init_0 = []
            init_1 = []
            
            for v in relevant_vars_01:
                if v[1] not in init_model:
                    continue
                val = init_model[v[1]]
                full_model[TS.get_timed(v[2], t)] = val
                init_0.append(EqualsOrIff(v[0], val))
                init_1.append(EqualsOrIff(v[1], val))

            init_0 = And(init_0)

            if cover != TRUE():
                init_1 = And(init_1)

                self._add_assertion(self.solver, init_1)
                self._add_assertion(self.solver, cover_1)

                res_cont = self._solve(self.solver)

                if res_cont:
                    Logger.log('Reached cover in no unroll simulation at k=%s'%(t), 2)
                    model = init_model
                    return (t, full_model)
                else:
                    Logger.log('Cover not reached at k=%s'%t, 2)

            if inc:
                self._pop(self.solver)
                
        return (t, full_model)


