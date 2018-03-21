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

from pysmt.shortcuts import And, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, get_free_variables
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.rewritings import conjunctive_partition

from cosa.util.logger import Logger
from cosa.core.transition_system import TS, HTS
from cosa.core.coreir_parser import SEP

from cosa.printers import TextTracePrinter, VCDTracePrinter

import copy

NL = "\n"

S1 = "sys1"+SEP
S2 = "sys2"+SEP

FWD = "FWD"
BWD = "BWD"
ZZ  = "ZZ"

class BMCConfig(object):

    incremental = True
    strategy = None
    solver = None
    full_trace = False
    prefix = None
    smt2file = None
    
    def __init__(self):
        self.incremental = True
        self.strategy = FWD
        self.solver = Solver(name="z3")
        self.full_trace = False
        self.prefix = None
        self.smt2file = None
    
        self.strategies = BMCConfig.get_strategies()

    @staticmethod
    def get_strategies():
        strategies = []
        strategies.append((FWD, "Forward reachability"))
        strategies.append((BWD, "Backward reachability"))
        strategies.append((ZZ,  "Mixed Forward and Backward reachability (Zig-Zag)"))

        return strategies
            
class BMC(object):

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

    def at_time(self, vars, trans, t):
        varmap_t  = [(v, TS.get_timed(v, t)) for v in vars]
        varmap_tp = [(TS.get_prime(v), TS.get_timed(v, t+1)) for v in vars]

        varmap = dict(varmap_t + varmap_tp)

        return trans.substitute(varmap)

    def at_ptime(self, vars, trans, t):
        varmap_t  = [(v, TS.get_ptimed(v, t+1)) for v in vars]
        varmap_tp = [(TS.get_prime(v), TS.get_ptimed(v, t)) for v in vars]

        varmap = dict(varmap_t + varmap_tp)

        return trans.substitute(varmap)
    
    def unroll(self, trans, invar, k_end, k_start=0):
        Logger.log("Unroll from %s to %s"%(k_start, k_end), 2)

        vars = [v for v in And(trans, invar).get_free_variables() if not TS.is_prime(v)]
        fwd = k_start <= k_end
        time_function = self.at_time if fwd else self.at_ptime
        (k_start, k_end) = (min(k_start, k_end), max(k_start, k_end))

        formula = TRUE()        
        t = k_start
        while t < k_end:
            to_t = t+1 if fwd else t
            formula = And(formula, time_function(vars, trans, t))
            formula = And(formula, time_function(vars, invar, to_t))
            Logger.log("Add trans, k=%s"%t, 2)
            t += 1

        return formula

    def print_trace(self, hts, model, length, xvars=None, diff_only=True):
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
            trace = printer.print_trace(hts, model, length)
            
            Logger.log(trace, 0)
        else:
            printer = VCDTracePrinter()
            trace = printer.print_trace(hts, model, length)
            
            BMC.TraceID += 1
            trace_file = "%s-id_%s%s"%(self.config.prefix, BMC.TraceID, printer.get_file_ext())
            with open(trace_file, "w") as f:
                f.write(trace)

    def equivalence(self, hts2, k, symbolic_init):
        (htseq, t, model) = self.combined_system(hts2, k, symbolic_init, True)
            
        if t > -1:
            Logger.log("Systems are NOT equivalent", 0)
            self.print_trace(htseq, model, t, None, False)
        else:
            Logger.log("Systems are equivalent with k=%s"%k, 0)
            

    def fsm_check(self):
        (htseq, t, model) = self.combined_system(self.hts, 1, True, False)
            
        if t > -1:
            Logger.log("FSM is NOT deterministic", 0)            
            self.print_trace(htseq, model, t, None, False)
        else:
            Logger.log("FSM is deterministic", 0)
            
                
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

        if inc:
            (t, model) = self.solve(htseq, miter_out, k)
            model = self.__remap_model(htseq.vars, model, k)
        else:
            (t, model) = self.solve_fwd(htseq, miter_out, k, False)

        return (htseq, t, model)


    def simulate(self, prop, k):
        if prop == TRUE():
            self.config.incremental = False
            (t, model) = self.solve_fwd(self.hts, Not(prop), k, False)
        else:
            (t, model) = self.solve(self.hts, Not(prop), k)

        model = self.__remap_model(self.hts.vars, model, t)
        
        if t > -1:
            Logger.log("Execution found", 0)
            self.print_trace(self.hts, model, t, prop.get_free_variables())
            return True
        else:
            Logger.log("Deadlock wit k=%s"%k, 0)
            return False

    def solve(self, hts, prop, k):
        if self.config.incremental:
            return self.solve_inc(hts, prop, k)

        return self.solve_fwd(hts, prop, k)
            
    def solve_inc(self, hts, prop, k):
        if self.config.strategy == FWD:
            return self.solve_inc_fwd(hts, prop, k)
        
        if self.config.strategy == BWD:
            return self.solve_inc_bwd(hts, prop, k)

        if self.config.strategy == ZZ:
            return self.solve_inc_zz(hts, prop, k)
        
        return None

    def solve_fwd(self, hts, prop, k, shortest=True):

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        t_start = 0 if shortest else k
        
        t = 0 if shortest else k
        while (t < k+1):
            self.__reset_assertions(self.config.solver)

            formula = And(init, invar)
            formula = self.at_time(hts.vars, formula, 0)
            Logger.log("Add init and invar", 2)
            self.__add_assertion(self.config.solver, formula)

            trans_t = self.unroll(trans, invar, t)
            self.__add_assertion(self.config.solver, trans_t)
            
            propt = Not(self.at_time(hts.vars, prop, t))
            Logger.log("Add property time %d"%t, 2)
            self.__add_assertion(self.config.solver, propt)

            res = self.__solve(self.config.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.config.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))
                
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)
    
    def solve_inc_fwd(self, hts, prop, k):
        self.__reset_assertions(self.config.solver)

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        formula = And(init, invar)
        formula = self.at_time(hts.vars, formula, 0)
        Logger.log("Add init and invar", 2)
        self.__add_assertion(self.config.solver, formula)
        
        t = 0 
        while (t < k+1):
            self.__push(self.config.solver)
            
            propt = Not(self.at_time(hts.vars, prop, t))
            Logger.log("Add not property at time %d"%t, 2)
            self.__add_assertion(self.config.solver, propt)

            res = self.__solve(self.config.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.config.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self.__pop(self.config.solver)
            
            trans_t = self.unroll(trans, invar, t+1, t)
            self.__add_assertion(self.config.solver, trans_t)

            if self.assert_property:
                prop_t = self.unroll(TRUE(), prop, t, t-1)
                self.__add_assertion(self.config.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)

            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)
    
    def solve_inc_bwd(self, hts, prop, k):
        self.__reset_assertions(self.config.solver)

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        formula = self.at_ptime(hts.vars, And(Not(prop), invar), -1)
        Logger.log("Add not property at time %d"%0, 2)
        self.__add_assertion(self.config.solver, formula)

        t = 0 
        while (t < k+1):
            self.__push(self.config.solver)

            pinit = self.at_ptime(hts.vars, init, t-1)
            Logger.log("Add init at time %d"%t, 2)
            self.__add_assertion(self.config.solver, pinit)

            res = self.__solve(self.config.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.config.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self.__pop(self.config.solver)
            
            trans_t = self.unroll(trans, invar, t, t+1)
            self.__add_assertion(self.config.solver, trans_t)

            if self.assert_property and t > 0:
                prop_t = self.unroll(TRUE(), prop, t-1, t)
                self.__add_assertion(self.config.solver, prop_t)
                Logger.log("Add property at time %d"%t, 2)
            
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)
        
    def solve_inc_zz(self, hts, prop, k):
        self.__reset_assertions(self.config.solver)

        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        initt = self.at_time(hts.vars, And(init, invar), 0)
        Logger.log("Add init at_0", 2)
        self.__add_assertion(self.config.solver, initt)
        
        propt = self.at_ptime(hts.vars, And(Not(prop), invar), -1)
        Logger.log("Add property pat_%d"%0, 2)
        self.__add_assertion(self.config.solver, propt)
        
        t = 0 
        while (t < k+1):
            self.__push(self.config.solver)
            even = (t % 2) == 0
            th = int(t/2)

            if even:
                eq = And([EqualsOrIff(self.at_time(hts.vars, v, th), self.at_ptime(hts.vars, v, th-1)) for v in hts.vars])
            else:
                eq = And([EqualsOrIff(self.at_time(hts.vars, v, th+1), self.at_ptime(hts.vars, v, th-1)) for v in hts.vars])
                
            Logger.log("Add equivalence time %d"%t, 2)
            self.__add_assertion(self.config.solver, eq)

            res = self.__solve(self.config.solver)

            if res:
                Logger.log("Counterexample found with k=%s"%(t), 1)
                model = self.config.solver.get_model()
                Logger.log("", 0, not(Logger.level(1)))
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self.__pop(self.config.solver)

            if even: 
                trans_t = self.unroll(trans, invar, th+1, th)
            else:
                trans_t = self.unroll(trans, invar, th, th+1)

            self.__add_assertion(self.config.solver, trans_t)
                
            t += 1
        Logger.log("", 0, not(Logger.level(1)))
                
        return (-1, None)
            
    def safety(self, prop, k):
        (t, model) = self.solve(self.hts, prop, k)

        model = self.__remap_model(self.hts.vars, model, t)
        
        if t > -1:
            Logger.log("Property is FALSE", 0)
            self.print_trace(self.hts, model, t, prop.get_free_variables())
            return False
        else:
            Logger.log("No counterexample found", 0)
            return True

    def __remap_model(self, vars, model, k):
        if model is None:
            return model
        
        if self.config.strategy == BWD:
            return self.__remap_model_bwd(vars, model, k)

        if self.config.strategy == ZZ:
            return self.__remap_model_zz(vars, model, k)

        if self.config.strategy == FWD:
            return self.__remap_model_fwd(vars, model, k)
        
        return None
        
    def __remap_model_fwd(self, vars, model, k):
        return model

    def __remap_model_bwd(self, vars, model, k):
        retmodel = dict()
        
        for var in vars:
            for t in range(k+1):
                retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]

        return retmodel

    def __remap_model_zz(self, vars, model, k):
        retmodel = dict(model)

        for var in vars:
            for t in range(int(k/2)+1, k+1, 1):
                retmodel[TS.get_timed(var, t)] = model[TS.get_ptimed(var, k-t)]
                
        return retmodel

    def __write_smt2_log(self, line):
        if self.config.smt2file is not None:
            with open(self.config.smt2file, "a") as f:
                f.write(line+"\n")
    
    def __add_assertion(self, solver, formula):
        solver.add_assertion(formula)
        if Logger.level(3):
            buf = cStringIO()
            printer = SmtPrinter(buf)
            printer.printer(formula)
            print(buf.getvalue()+"\n")

        if self.config.smt2file is not None:
            for v in set(formula.get_free_variables()).difference(self.smtvars):
                if v.symbol_type() == BOOL:
                    self.__write_smt2_log("(declare-fun %s () Bool)" % (v.symbol_name()))
                else:
                    self.__write_smt2_log("(declare-fun %s () (_ BitVec %s))" % (v.symbol_name(), v.symbol_type().width))

            self.__write_smt2_log("")
            self.smtvars = set(formula.get_free_variables()).union(self.smtvars)

            if formula.is_and():
                for f in conjunctive_partition(formula):
                    buf = cStringIO()
                    printer = SmtPrinter(buf)
                    printer.printer(f)
                    self.__write_smt2_log("(assert %s)"%buf.getvalue())
            else:
                buf = cStringIO()
                printer = SmtPrinter(buf)
                printer.printer(formula)
                self.__write_smt2_log("(assert %s)"%buf.getvalue())
                    
                    
    def __push(self, solver):
        solver.push()

        self.__write_smt2_log("(push 1)")
        
    def __pop(self, solver):
        solver.pop()

        self.__write_smt2_log("(pop 1)")

    def __reset_assertions(self, solver):
        solver.reset_assertions()

        if self.config.smt2file is not None:
            with open(self.config.smt2file, "w") as f:
                f.write("(set-logic QF_BV)\n")

    def __solve(self, solver):
        self.__write_smt2_log("(check-sat)")
        self.__write_smt2_log("")
        
        if self.config.skip_solving:
            return None
            
        if Logger.level(1):
            timer = Logger.start_timer("Solve")

        r = solver.solve()
        
        if Logger.level(1):
            self.total_time += Logger.stop_timer(timer)
            Logger.log("Total time: %.2f sec"%self.total_time, 1)
            
        return r
