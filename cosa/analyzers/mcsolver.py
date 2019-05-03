# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from six.moves import cStringIO

from pysmt.shortcuts import BV, And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify, BVAdd, BVUGE
from pysmt.rewritings import conjunctive_partition
from pysmt.smtlib.printers import SmtDagPrinter
from pysmt.logics import convert_logic_from_string, QF_BV, QF_ABV

from cosa.utils.logger import Logger
from cosa.representation import TS, HTS
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.printers.trace import TextTracePrinter, VCDTracePrinter
from cosa.problem import Trace
from cosa.utils.generic import status_bar

class VerificationStrategy(object):
    FWD = "FWD"
    BWD = "BWD"
    ZZ  = "ZZ"
    NU  = "NU"
    INT  = "INT"
    LTL  = "LTL"
    AUTO = "AUTO"
    ALL = "ALL"
    MULTI = "MULTI"

# strategies should be registered here to be visible from command line options
def get_verification_strategies():
    strategies = []
    strategies.append((VerificationStrategy.AUTO,  "Automatic selection"))
    strategies.append((VerificationStrategy.MULTI, "Parallel multiple techniques"))
    strategies.append((VerificationStrategy.FWD,   "Forward reachability"))
    strategies.append((VerificationStrategy.BWD,   "Backward reachability"))
    strategies.append((VerificationStrategy.ZZ,    "Mixed Forward and Backward reachability (Zig-Zag)"))
    strategies.append((VerificationStrategy.INT,   "Interpolation"))
    strategies.append((VerificationStrategy.NU,    "States picking without unrolling (only for simulation)"))
    strategies.append((VerificationStrategy.LTL,   "Pure LTL verification (without optimizations)"))
    strategies.append((VerificationStrategy.ALL,   "Use all techniques"))
    return strategies

class TraceSolver(object):

    solver_name = None
    name = None
    logic = None
    incremental = None
    solver_options = None
    basename = None
    trace_file = None
    solver = None
    smt2vars = None
    smt2vars_inc = None

    def __init__(self, solver_name, name, logic, incremental, solver_options, basename=None):
        self.solver_name = solver_name
        self.name = name
        self.logic = logic
        self.incremental = incremental
        self.solver_options = solver_options
        self.basename = basename
        self.smt2vars = set([])
        self.solver = Solver(name=solver_name, logic=logic, incremental=incremental, solver_options=solver_options)
        self.smt2vars_inc = []
        if basename is not None:
            self.trace_file = "%s-%s.smt2"%(basename, name)

    def clear(self):
        self.solver.exit()
        self.solver = Solver(name=self.solver_name, logic=self.logic, incremental=self.incremental, solver_options=self.solver_options)

    def copy(self, name=None):
        return TraceSolver(self.solver_name, self.name if name is None else name, self.logic, self.incremental, self.solver_options, self.basename)

class BMCSolver(object):

    def __init__(self, hts, config):
        self.hts = hts
        self.config = config

        self.assert_property = False

        Logger.time = True
        self.total_time = 0.0

        basename = None
        if self.config.smt2_tracing is not None:
            basename = ".".join(self.config.smt2_tracing.split(".")[:-1])
        logic = convert_logic_from_string(self.hts.logic)
        self.solver = TraceSolver(config.solver_name, "main", logic=logic, incremental=config.incremental,
                                  solver_options=config.solver_options, basename=basename)

        self.varmapf_t = None
        self.varmapb_t = None

    def unroll(self, trans, invar, k_end, k_start=0, gen_list=False):
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

        if gen_list:
            return formula

        return And(formula)

    def _remap_model(self, vars, model, k):
        if model is None:
            return model

        if self.config.strategy == VerificationStrategy.BWD:
            return self._remap_model_bwd(vars, model, k)

        if self.config.strategy == VerificationStrategy.ZZ:
            return self._remap_model_zz(vars, model, k)

        if self.config.strategy in [VerificationStrategy.AUTO, \
                                    VerificationStrategy.FWD, \
                                    VerificationStrategy.NU, \
                                    VerificationStrategy.INT, \
                                    VerificationStrategy.LTL, \
                                    VerificationStrategy.ALL, \
                                    VerificationStrategy.MULTI]:
            return self._remap_model_fwd(vars, model, k)

        Logger.error("Invalid configuration strategy")
        return None

    def _init_at_time(self, vars, maxtime):

        previous = self.config.strategy != VerificationStrategy.FWD

        if self.varmapf_t is not None:
            del(self.varmapf_t)

        if self.varmapb_t is not None:
            del(self.varmapb_t)

        self.varmapf_t = {}
        self.varmapb_t = {}

        timed = TS.get_timed_name
        ptimed = TS.get_ptimed_name
        prime = TS.get_prime_name
        prev = TS.get_prev_name

        varsstr = [v.symbol_name() for v in vars]

        for t in range(maxtime+2):
            varmapf = []
            varmapb = []

            for sname in varsstr:
                psname = prime(sname)
                rsname = prev(sname)

                varmapf.append((sname, timed(sname, t)))
                varmapf.append((psname, timed(sname, t+1)))
                varmapf.append((rsname, timed(sname, t-1)))

                if previous:
                    varmapb.append((sname, ptimed(sname, t)))
                    varmapb.append((psname, ptimed(sname, t-1)))
                    varmapb.append((rsname, ptimed(sname, t+1)))

            self.varmapf_t[t] = dict(varmapf)

            if previous:
                self.varmapb_t[t-1] = dict(varmapb)

    def at_time(self, formula, t):
        return substitute(formula, self.varmapf_t[t])

    def at_ptime(self, formula, t):
        return substitute(formula, self.varmapb_t[t])

    def _write_smt2_log(self, solver, line):
        # don't include any escape characters in smt2 output
        # they can't be quoted away with "|" and should only
        # be a part of a name, because auto-generated names don't
        # use escape characters
        line = line.replace("\\", "")
        tracefile = solver.trace_file
        if tracefile is not None:
            with open(tracefile, "a") as f:
                f.write(line+"\n")

    def _write_smt2_comment(self, solver, line):
        return self._write_smt2_log(solver, ";; %s"%line)


    def _formula_to_smt2(self, formula):
        buf = cStringIO()
        printer = SmtDagPrinter(buf)
        printer.printer(formula)
        return buf.getvalue()
    
    def _add_assertion(self, solver, formula, comment=None):
        if not self.config.skip_solving:
            solver.solver.add_assertion(formula)

        if Logger.level(3):
            print(self._formula_to_smt2(formula)+"\n")

        if solver.trace_file is not None:
            if comment:
                self._write_smt2_comment(solver, "%s: START"%comment)

            formula_fv = get_free_variables(formula)

            for v in formula_fv:
                if v in solver.smt2vars:
                    continue

                symbol_name = self._formula_to_smt2(v)
                if v.symbol_type() == BOOL:
                    self._write_smt2_log(solver, "(declare-fun %s () Bool)" % (symbol_name))
                elif v.symbol_type().is_array_type():
                    st = v.symbol_type()
                    assert st.index_type.is_bv_type(), "Expecting BV indices"
                    assert st.elem_type.is_bv_type(), "Expecting BV elements"
                    self._write_smt2_log(solver, "(declare-fun %s () (Array (_ BitVec %s) (_ BitVec %s)))"%(symbol_name, st.index_type.width, st.elem_type.width))
                elif v.symbol_type().is_bv_type():
                    self._write_smt2_log(solver, "(declare-fun %s () (_ BitVec %s))" % (symbol_name, v.symbol_type().width))
                else:
                    Logger.error("Unhandled type in smt2 translation")

            self._write_smt2_log(solver, "")

            for v in formula_fv:
                solver.smt2vars.add(v)

            if formula.is_and():
                for f in conjunctive_partition(formula):
                    self._write_smt2_log(solver, "(assert %s)"%self._formula_to_smt2(f))
            else:
                self._write_smt2_log(solver, "(assert %s)"%self._formula_to_smt2(formula))

            if comment:
                self._write_smt2_comment(solver, "%s: END"%comment)


    def _push(self, solver):
        Logger.log("Push solver \"%s\""%solver.name, 2)
        if not self.config.skip_solving:
            solver.solver.push()

        solver.smt2vars_inc.append(solver.smt2vars)
        self._write_smt2_log(solver, "(push 1)")

    def _pop(self, solver):
        Logger.log("Pop solver \"%s\""%solver.name, 2)
        if not self.config.skip_solving:
            solver.solver.pop()

        solver.smt2vars = solver.smt2vars_inc.pop()
        self._write_smt2_log(solver, "(pop 1)")

    def _get_model(self, solver, relevant_vars=None):
        if relevant_vars is None:
            return dict(solver.solver.get_model())

        return dict([(v, solver.solver.get_value(v)) for v in relevant_vars])

    def _reset_assertions(self, solver, clear=False):
        if clear:
            solver.clear()
        if not self.config.skip_solving:
            solver.solver.reset_assertions()

        if solver.trace_file is not None:
            solver.smt2vars = set([])
            with open(solver.trace_file, "w") as f:
                f.write("(set-logic %s)\n"%self.hts.logic)

    def _solve(self, solver):
        Logger.log("Solve solver \"%s\""%solver.name, 2)

        self._write_smt2_log(solver, "(check-sat)")
        self._write_smt2_log(solver, "")

        if self.config.skip_solving:
            return None

        if Logger.level(2):
            timer = Logger.start_timer("Solve")

        r = solver.solver.solve()

        if Logger.level(2):
            self.total_time += Logger.get_timer(timer)
            Logger.log("Total time solve: %.2f sec"%self.total_time, 1)

        return r


    def _check_lemma(self, hts, lemma, init, trans):

        def check_init():
            self._reset_assertions(self.solver)
            self._add_assertion(self.solver, self.at_time(And(init, Not(lemma)), 0), comment="Init check")
            res = self._solve(self.solver)

            if res:
                Logger.log("Lemma \"%s\" failed for I -> L"%lemma, 2)
                return False

            Logger.log("Lemma \"%s\" holds for I -> L"%lemma, 2)
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

        for lemma in holding_lemmas:
            hts.add_assumption(lemma)
        return (hts, False)

    def _remap_model_fwd(self, vars, model, k):
        return model

    def _remap_model_bwd(self, vars, model, k):
        retmodel = dict()

        for var in vars:
            for t in range(k+1):
                if TS.get_ptimed(var, k-t) in model:
                    retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]

        return retmodel

    def _remap_model_zz(self, vars, model, k):
        retmodel = dict([el for el in dict(model).items() if not TS.is_ptimed(el[0])])

        for var in vars:
            for t in range(int(k/2)+1, k+1, 1):
                retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]

        return retmodel

    def generate_trace(self, \
                       model, \
                       length, \
                       xvars=None, \
                       find_loop=False):

        trace = Trace()
        trace.model = model
        trace.length = length
        trace.infinite = find_loop
        trace.prop_vars = xvars

        return trace

# used elsewhere to enable/disable features
# there's not a great way to query pysmt for this except
# from pysmt.solvers import cvc4
# cvc4.CVC4Solver.LOGICS
# which requires that cvc4 is installed, and since this won't change
# often it's more efficent to hardcode it, instead of repeating for each
# solver and catching exceptions
CONST_ARRAYS_SUPPORT = {"cvc4", "msat", "z3"}

