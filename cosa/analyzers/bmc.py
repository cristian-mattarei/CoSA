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
import copy
from six.moves import cStringIO

from pysmt.shortcuts import And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify
from pysmt.typing import _BVType, ArrayType
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.rewritings import conjunctive_partition, disjunctive_partition

from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.transition_systems import TS, HTS
from cosa.encoders.coreir import CoreIRParser, SEP

from cosa.printers import TextTracePrinter, VCDTracePrinter
from cosa.problem import VerificationStatus

from cosa.analyzers.mcsolver import TraceSolver, MCSolver, FWD, BWD, ZZ, NU

NL = "\n"

S1 = "sys1"+SEP
S2 = "sys2"+SEP

class BMC(MCSolver):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0
    tracefile = None

    def __init__(self, hts, config):
        self.hts = hts
        self.config = config

        self.assert_property = False

        Logger.time = True
        self.total_time = 0.0

        self.solver = TraceSolver(config.solver_name)
        if self.config.prove:
            self.solver_2 = TraceSolver(config.solver_name)

        self._reset_smt2_tracefile()

        self.varmapf_t = None
        self.varmapb_t = None

    def unroll(self, trans, invar, k_end, k_start=0):
        Logger.log("Unroll from %s to %s"%(k_start, k_end), 2)

        fwd = k_start <= k_end
        time_function = self.at_time if fwd else self.at_ptime
        (k_start, k_end) = (min(k_start, k_end), max(k_start, k_end))

        formula = []
        t = k_start
        while t < k_end:
            to_t = t+1 if fwd else t
            formula.append(time_function(trans, t))
            formula.append(time_function(invar, to_t))
            Logger.log("Add trans, k=%s"%t, 2)
            t += 1

        return And(formula)

    def simple_path(self, vars_, k_end, k_start=0):
        Logger.log("Simple path from %s to %s"%(k_start, k_end), 2)

        if k_end == k_start:
            return TRUE()

        def not_eq_states(vars1, vars2):
            assert len(vars1) == len(vars2)
            eqvars = []
            for i in range(len(vars1)):
                eqvars.append(Not(EqualsOrIff(vars1[i], vars2[i])))
            return Or(eqvars)

        lvars = list(vars_)
        end_vars = [TS.get_timed(v, k_end) for v in lvars]
        
        formula = []
        for t in range(k_start, k_end, 1):
            formula.append(not_eq_states(end_vars, [TS.get_timed(v, t) for v in lvars]))

        return And(formula)

    def print_trace(self, hts, model, length, \
                    xvars=None, \
                    diff_only=True, \
                    map_function=None, \
                    prefix=None, \
                    write_to_file=True, \
                    find_loop=False):
        trace = []
        prevass = []

        if prefix is None:
            prefix = self.config.prefix

        full_trace = self.config.full_trace

        if write_to_file:
            diff_only = False

        if Logger.level(1):
            diff_only = False
            full_trace = True

        # Human Readable Format
        hr_printer = TextTracePrinter()
        hr_printer.extra_vars = xvars
        hr_printer.diff_only = diff_only
        hr_printer.full_trace = full_trace
        hr_trace = hr_printer.print_trace(hts, model, length, map_function, find_loop)

        # VCD format
        vcd_trace = None
        if self.config.vcd_trace:
            vcd_printer = VCDTracePrinter()
            vcd_trace = vcd_printer.print_trace(hts, model, length, map_function)

        vcd_trace_file = None
        hr_trace_file = None

        return (hr_trace, vcd_trace)

    def fsm_check(self):
        (htseq, t, model) = self.combined_system(self.hts, 1, True, False)

        self._init_at_time(htseq.vars, k)

        if t > -1:
            Logger.log("FSM is NOT deterministic", 0)
            self.print_trace(htseq, model, t, None, False, map_function=self.config.map_function)
        else:
            Logger.log("FSM is deterministic", 0)


    # TODO: Deprecate this entirely. Need to update fsm_check
    def combined_system(self, hts2, k, symbolic_init, inc=True):
        htseq = HTS("eq")

        map1 = dict([(v, TS.get_prefix(v, S1)) for v in self.hts.vars]+[(TS.get_prime(v), TS.get_prefix(TS.get_prime(v), S1)) for v in self.hts.vars])
        map2 = dict([(v, TS.get_prefix(v, S2)) for v in self.hts.vars]+[(TS.get_prime(v), TS.get_prefix(TS.get_prime(v), S2)) for v in self.hts.vars])

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

        inputs = self.hts.inputs.intersection(hts2.inputs)
        outputs = self.hts.outputs.intersection(hts2.outputs)

        htseq.inputs = set([TS.get_prefix(v, S1) for v in self.hts.inputs]).union(set([TS.get_prefix(v, S2) for v in hts2.inputs]))
        htseq.outputs = set([TS.get_prefix(v, S1) for v in self.hts.outputs]).union(set([TS.get_prefix(v, S2) for v in hts2.outputs]))

        if symbolic_init:
            states = self.hts.state_vars.intersection(hts2.state_vars)
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

        if symbolic_init:
            eqmiteroutputs = Iff(miter_out, Implies(eqstates, eqoutputs))
        else:
            eqmiteroutputs = Iff(miter_out, eqoutputs)

        htseq.add_ts(TS(set([miter_out]), TRUE(), TRUE(), And(eqinputs, eqmiteroutputs)))
        self._init_at_time(htseq.vars, k)

        if inc:
            (t, model) = self.solve(htseq, miter_out, k)
            model = self._remap_model(htseq.vars, model, k)
        else:
            (t, model) = self.solve_fwd(htseq, miter_out, k, False)

        return (htseq, t, model)


    def simulate(self, prop, k):
        if self.config.strategy == NU:
            self._init_at_time(self.hts.vars, 1)
            (t, model) = self.sim_no_unroll(self.hts, prop, k)
        else:
            self._init_at_time(self.hts.vars, k)
            if prop == TRUE():
                self.config.incremental = False
                (t, model) = self.solve_fwd(self.hts, Not(prop), k, False)
            else:
                (t, model) = self.solve(self.hts, Not(prop), k)

        model = self._remap_model(self.hts.vars, model, t)

        if t > -1:
            Logger.log("Execution found", 1)
            trace = self.print_trace(self.hts, model, t, get_free_variables(prop), map_function=self.config.map_function)
            return (VerificationStatus.TRUE, trace)
        else:
            Logger.log("Deadlock wit k=%s"%k, 1)
            return (VerificationStatus.FALSE, None)

    def solve(self, hts, prop, k, k_min=0, lemmas=None):
        if lemmas is not None:
            (hts, res) = self.add_lemmas(hts, prop, lemmas)
            if res:
                Logger.log("Lemmas imply the property", 1)
                Logger.log("", 0, not(Logger.level(1)))
                return (0, True)

        if self.config.incremental:
            return self.solve_inc(hts, prop, k, k_min, lemmas)

        return self.solve_fwd(hts, prop, k)

    def solve_inc(self, hts, prop, k, k_min, lemmas=None):
        if self.config.strategy == FWD:
            return self.solve_inc_fwd(hts, prop, k, k_min, lemmas)

        if self.config.strategy == BWD:
            return self.solve_inc_bwd(hts, prop, k)

        if self.config.strategy == ZZ:
            return self.solve_inc_zz(hts, prop, k)

        Logger.error("Invalid configuration strategy")

        return None

    def solve_fwd(self, hts, prop, k, shortest=True):

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        # trans = And(trans, self._update_trans_prev(prop))

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

            res = self._solve(self.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.solver.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            t += 1
        Logger.log("", 0, not(Logger.level(1)))

        return (-1, None)
    
    def _check_lemma(self, hts, lemma):
        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()
        trans = And(trans, invar, TS.to_next(invar))
        init = And(init, invar)

        def check_init():
            self._reset_assertions(self.solver)
            check_1 = Not(Implies(init, lemma))
            check_1 = self.at_time(check_1, 0)
            self._add_assertion(self.solver, check_1, comment="Init check")
            res = self._solve(self.solver)

            prefix = None
            if self.config.prefix is not None:
                prefix = self.config.prefix+"-ind"

            if res:
                if Logger.level(2):
                    Logger.log("Lemma \"%s\" failed for I -> L"%lemma, 2)
                    (hr_trace, vcd_trace) = self.print_trace(hts, self.solver.solver.get_model(), 1, prefix=prefix, map_function=self.config.map_function)
                    Logger.log("", 2)
                    if hr_trace:
                        Logger.log("Counterexample: \n%s"%(hr_trace), 2)
                    else:
                        Logger.log("", 2)
                return False
            else:
                Logger.log("Lemma \"%s\" holds for I -> L"%lemma, 2)

            return True

        def check_step():
            self._reset_assertions(self.solver)

            check_2 = And(trans, lemma, Not(TS.to_next(lemma)))
            check_2 = self.at_time(check_2, 0)
            self._add_assertion(self.solver, check_2, comment="Trans check")
            res = self._solve(self.solver)

            if res:
                if Logger.level(2):
                    Logger.log("Lemma \"%s\" failed for L & T -> L'"%lemma, 2)
                    if Logger.level(3):
                        (hr_trace, vcd_trace) = self.print_trace(hts, self.solver.solver.get_model(), 1, prefix=prefix, map_function=self.config.map_function)
                        if hr_trace or vcd_trace:
                            vcd_msg = ""
                            if vcd_trace:
                                vcd_msg = " and in \"%s\""%(vcd_trace)
                            Logger.log("Counterexample stored in \"%s\"%s"%(hr_trace, vcd_msg), 2)
                        else:
                            Logger.log("", 2)
                return False
            else:
                Logger.log("Lemma \"%s\" holds for L & T -> L'"%lemma, 2)

            return True


        if not check_step():
            return False
        if not check_init():
            return False
                
        return True

    def _suff_lemmas(self, prop, lemmas):
        self._reset_assertions(self.solver)

        check_1 = Not(Implies(And(lemmas), prop))
        self._add_assertion(self.solver, check_1)
        res = self._solve(self.solver)

        if res:
            return False

        return True

    def add_lemmas(self, hts, prop, lemmas):
        if len(lemmas) == 0:
            return (hts, False)
        
        self._reset_assertions(self.solver)

        holding_lemmas = []
        lindex = 1
        nlemmas = len(lemmas)
        for lemma in lemmas:
            Logger.log("\nChecking Lemma %s/%s"%(lindex,nlemmas), 1)
            if self._check_lemma(hts, lemma):
                holding_lemmas.append(lemma)
                Logger.log("Lemma %s holds"%(lindex), 1)
                Logger.msg("L", 0, not(Logger.level(1)))
                
                if self._suff_lemmas(prop, holding_lemmas):
                    return (hts, True)
            else:
                Logger.log("Lemma %s does not hold"%(lindex), 1)
                Logger.msg("_", 0, not(Logger.level(1)))
            lindex += 1


        hts.assumptions = And(holding_lemmas)

        return (hts, False)

    def solve_inc_fwd(self, hts, prop, k, k_min, lemmas=None):
        self._reset_assertions(self.solver)

        if self.config.prove:
            self._reset_assertions(self.solver_2)

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        if self.config.simplify:
            Logger.log("Simplifying the Transition System", 1)
            if Logger.level(2):
                timer = Logger.start_timer("Simplify")

            init = simplify(init)
            trans = simplify(trans)
            invar = simplify(invar)
            if Logger.level(2):
                Logger.get_timer(timer)

        propt = FALSE()
        formula = And(init, invar)
        formula = self.at_time(formula, 0)
        Logger.log("Add init and invar", 2)
        self._add_assertion(self.solver, formula)

        if self.config.prove:
            # add invariants at time 0, but not init
            self._add_assertion(self.solver_2, self.at_time(invar, 0))

        next_prop = TS.has_next(prop)
        if next_prop:
            if k < 1:
                Logger.error("Invariant checking with next variables requires at least k=1")
            k_min = 1

        t = 0
        while (t < k+1):
            self._push(self.solver)

            if k_min > 0:
                t_prop = t-1 if next_prop else t
                if (not next_prop) or (next_prop and t>0):
                    propt = Or(propt, self.at_time(Not(prop), t_prop))
            else:
                propt = self.at_time(Not(prop), t)

            Logger.log("Add not property at time %d"%t, 2)
            self._add_assertion(self.solver, propt)

            if t >= k_min:
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
                Logger.log("\nSkipping solving for k=%s (k_min=%s)"%(t,k_min), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self._pop(self.solver)

            trans_t = self.unroll(trans, invar, t+1, t)
            self._add_assertion(self.solver, trans_t)

            if self.config.prove:
                self._add_assertion(self.solver_2, trans_t)
                self._add_assertion(self.solver_2, self.simple_path(self.hts.vars, t))

                self._push(self.solver_2)
                self._add_assertion(self.solver_2, self.at_time(Not(prop), t))

                if t >= k_min:
                    res = self._solve(self.solver_2)

                    if res:
                        Logger.log("Induction failed with k=%s"%(t), 1)
                    else:
                        Logger.log("Induction holds with k=%s"%(t), 1)
                        Logger.log("", 0, not(Logger.level(1)))
                        return (t, True)

                self._pop(self.solver_2)
                self._add_assertion(self.solver_2, self.at_time(prop, t))

            if self.assert_property:
                prop_t = self.unroll(TRUE(), prop, t, t-1)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)

            t += 1
        Logger.log("", 0, not(Logger.level(1)))

        return (-1, None)

    def solve_inc_bwd(self, hts, prop, k):
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

            res = self._solve(self.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.solver.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self._pop(self.solver)

            trans_t = self.unroll(trans, invar, t, t+1)
            self._add_assertion(self.solver, trans_t)

            if self.assert_property and t > 0:
                prop_t = self.unroll(TRUE(), prop, t-1, t)
                self._add_assertion(self.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)

            t += 1
        Logger.log("", 0, not(Logger.level(1)))

        return (-1, None)

    def solve_inc_zz(self, hts, prop, k):
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

            res = self._solve(self.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.solver.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
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
        Logger.log("", 0, not(Logger.level(1)))

        return (-1, None)

    def safety(self, prop, k, k_min):
        lemmas = self.hts.lemmas
        self._init_at_time(self.hts.vars, k)
        (t, model) = self.solve(self.hts, prop, k, k_min, lemmas)

        if model == True:
            return (VerificationStatus.TRUE, None, t)
        elif t > -1:
            model = self._remap_model(self.hts.vars, model, t)
            trace = self.print_trace(self.hts, model, t, get_free_variables(prop), map_function=self.config.map_function)
            return (VerificationStatus.FALSE, trace, t)
        else:
            return (VerificationStatus.UNK, None, t)

    def _remap_model(self, vars, model, k):
        if model is None:
            return model

        if self.config.strategy == BWD:
            return self._remap_model_bwd(vars, model, k)

        if self.config.strategy == ZZ:
            return self._remap_model_zz(vars, model, k)

        if self.config.strategy in [FWD, NU]:
            return self._remap_model_fwd(vars, model, k)

        Logger.error("Invalid configuration strategy")
        return None

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
            relevant_vars = self.hts.vars
        else:
            relevant_vars = self.hts.state_vars | self.hts.inputs | self.hts.outputs
        
        relevant_vars_0 = [TS.get_timed(v, 0) for v in relevant_vars]
        relevant_vars_1 = [TS.get_timed(v, 1) for v in relevant_vars]

        relevant_vars_01 = [(TS.get_timed(v, 0), TS.get_timed(v, 1), v) for v in relevant_vars]
        
        self._reset_assertions(self.solver)
        
        # Picking Initial State
        Logger.log("\nSolving for k=0", 1)
        self._add_assertion(self.solver, And(init_0, invar_0))
        res = self._solve(self.solver)

        if res:
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
                Logger.log("", 0, not(Logger.level(1)))
                return (-1, full_model)

            # Use previous model as initial state for next sat call
            init_0 = []
            init_1 = []
            
            for v in relevant_vars_01:
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
                    Logger.log("", 0, not(Logger.level(1)))
                    return (t, full_model)
                else:
                    Logger.log('Cover not reached at k=%s'%t, 2)

            if inc:
                self._pop(self.solver)
                
        Logger.log("", 0, not(Logger.level(1)))
        return (t, full_model)


    def _remap_model_fwd(self, vars, model, k):
        return model

    def _remap_model_bwd(self, vars, model, k):
        retmodel = dict()

        for var in vars:
            for t in range(k+1):
                retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]

        return retmodel

    def _remap_model_zz(self, vars, model, k):
        retmodel = dict(model)

        for var in vars:
            for t in range(int(k/2)+1, k+1, 1):
                retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]

        return retmodel
