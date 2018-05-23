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
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter

from cosa.utils.logger import Logger
from cosa.transition_systems import TS, HTS
from cosa.utils.formula_mngm import substitute, get_free_variables

FWD = "FWD"
BWD = "BWD"
ZZ  = "ZZ"
NU  = "NU"
INT  = "INT"

class MCConfig(object):

    incremental = True
    strategy = None
    solver = None
    full_trace = False
    prefix = None
    smt2file = None
    simplify = False
    map_function = None
    solver_name = None
    vcd_trace = None
    prove = None

    def __init__(self):
        self.incremental = True
        self.strategy = FWD
        self.solver_name = "msat"
        self.full_trace = False
        self.prefix = None
        self.smt2file = None
        self.simplify = False
        self.map_function = None
        self.vcd_trace = False
        self.prove = False

        self.strategies = MCConfig.get_strategies()

    @staticmethod
    def get_strategies():
        strategies = []
        strategies.append((FWD, "Forward reachability"))
        strategies.append((BWD, "Backward reachability"))
        strategies.append((ZZ,  "Mixed Forward and Backward reachability (Zig-Zag)"))
        strategies.append((INT, "Interpolation"))
        strategies.append((NU,  "States picking without unrolling (only for simulation)"))

        return strategies


class TraceSolver(object):

    name = None
    trace_file = None
    solver = None
    smt2vars = None
    smt2vars_inc = None
    
    def __init__(self, name):
        self.name = name
        self.smt2vars = set([])
        self.solver = Solver(name=self.name)
        self.smt2vars_inc = []

    def clear(self):
        self.solver.exit()
        self.solver = Solver(self.name)

class MCSolver(object):

    def __init__(self, hts, config):
        pass


    def _init_at_time(self, vars, maxtime):

        previous = self.config.strategy != FWD

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
    
    def _reset_smt2_tracefile(self):
        if self.config.smt2file is not None:
            basename = ".".join(self.config.smt2file.split(".")[:-1])
            self.solver.trace_file = "%s.smt2"%basename
            if self.config.prove:
                self.solver_2.trace_file = "%s-ind.smt2"%basename

    def _write_smt2_log(self, solver, line):
        tracefile = solver.trace_file
        if tracefile is not None:
            with open(tracefile, "a") as f:
                f.write(line+"\n")

    def _write_smt2_comment(self, solver, line):
        return self._write_smt2_log(solver, ";; %s"%line)

    def _add_assertion(self, solver, formula, comment=None):
        if not self.config.skip_solving:
            solver.solver.add_assertion(formula)

        if Logger.level(3):
            buf = cStringIO()
            printer = SmtPrinter(buf)
            printer.printer(formula)
            print(buf.getvalue()+"\n")

        if solver.trace_file is not None:
            if comment:
                self._write_smt2_comment(solver, comment)

            formula_fv = get_free_variables(formula)
                
            for v in formula_fv:
                if v in solver.smt2vars:
                    continue
                
                if v.symbol_type() == BOOL:
                    self._write_smt2_log(solver, "(declare-fun %s () Bool)" % (v.symbol_name()))
                elif v.symbol_type().is_array_type():
                    st = v.symbol_type()
                    assert st.index_type.is_bv_type(), "Expecting BV indices"
                    assert st.elem_type.is_bv_type(), "Expecting BV elements"
                    self._write_smt2_log(solver, "(declare-fun %s () (Array (_ BitVec %s) (_ BitVec %s)))"%(v.symbol_name(), st.index_type.width, st.elem_type.width))
                elif v.symbol_type().is_bv_type():
                    self._write_smt2_log(solver, "(declare-fun %s () (_ BitVec %s))" % (v.symbol_name(), v.symbol_type().width))
                else:
                    raise RuntimeError("Unhandled type in smt2 translation")

            self._write_smt2_log(solver, "")

            for v in formula_fv:
                solver.smt2vars.add(v)

            if formula.is_and():
                for f in conjunctive_partition(formula):
                    buf = cStringIO()
                    printer = SmtPrinter(buf)
                    printer.printer(f)
                    self._write_smt2_log(solver, "(assert %s)"%buf.getvalue())
            else:
                buf = cStringIO()
                printer = SmtPrinter(buf)
                printer.printer(formula)
                self._write_smt2_log(solver, "(assert %s)"%buf.getvalue())


    def _push(self, solver):
        if not self.config.skip_solving:
            solver.solver.push()

        solver.smt2vars_inc.append(solver.smt2vars)
        self._write_smt2_log(solver, "(push 1)")

    def _pop(self, solver):
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
                
