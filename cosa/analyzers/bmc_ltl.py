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

from pysmt.shortcuts import And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL

from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.representation import TS
from cosa.encoders.ltl import LTLEncoder, verification_type

from cosa.problem import VerificationStatus, VerificationType
from cosa.analyzers.mcsolver import TraceSolver, BMCSolver, VerificationStrategy
from cosa.analyzers.bmc_temporal import BMCTemporal
from cosa.analyzers.bmc_safety import BMCSafety

class BMCLTL(BMCTemporal, BMCSafety):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0
    tracefile = None

    def __init__(self, hts, config):
        BMCSolver.__init__(self, hts, config)

        self.enc = LTLEncoder()

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

    def _init_v_time(self, vars, k):
        self.vars_time = []
        
        for t in range(k+1):
            vars_at_t = []
            for v in vars:
                vars_at_t.append((v, TS.get_timed_name(v, t)))
            self.vars_time.append((t, dict(vars_at_t)))
            
        self.vars_time = dict(self.vars_time)
    
    def ltl(self, prop, k, k_min=0):
        if self.config.strategy != VerificationStrategy.LTL:
            (vtype, prop) = verification_type(self.enc.to_nnf(prop))

            if vtype == VerificationType.SAFETY:
                return self.safety(prop, k, k_min)

            if vtype == VerificationType.LIVENESS:
                return self.liveness(prop, k, k_min)

            if vtype == VerificationType.EVENTUALLY:
                return self.eventually(prop, k, k_min)

        return self.ltl_generic(prop, k, k_min)
        
    def ltl_generic(self, prop, k, k_min=0):
        lemmas = self.hts.lemmas
        
        self._init_at_time(self.hts.vars, k)
        self._init_v_time(self.hts.vars, k)

        (t, model) = self.solve(self.hts, prop, k, lemmas)

        if model == True:
            return (VerificationStatus.TRUE, None, t)
        elif model is not None:
            model = self._remap_model(self.hts.vars, model, t)
            trace = self.generate_trace(model, t, get_free_variables(prop), find_loop=True)
            return (VerificationStatus.FALSE, trace, t)
        else:
            return (VerificationStatus.UNK, None, t)
        
    def solve(self, hts, prop, k, lemmas=None):
        if lemmas is not None:
            (hts, res) = self.add_lemmas(hts, prop, lemmas)
            if res:
                Logger.log("Lemmas imply the property", 1)
                Logger.log("", 0, not(Logger.level(1)))
                return (0, True)

        hts.reset_formulae()
        
        return self.solve_inc(hts, prop, k)

    def all_simple_loopbacks(self, vars, k):
        lvars = list(vars)
        vars_k = [TS.get_timed(v, k) for v in lvars]
        loopback = []
        eqvar = None
        heqvars = None

        peqvars = FALSE()
            
        for i in range(k):
            vars_i = [TS.get_timed(v, i) for v in lvars]
            eq_k_i = And([EqualsOrIff(vars_k[j], vars_i[j]) for j in range(len(lvars))])
                
            loopback.append(eq_k_i)

        loopback.append(FALSE())
        return loopback
    
    def solve_inc(self, hts, prop, k, all_vars=True):

        if all_vars:
            relevant_vars = hts.vars
        else:
            relevant_vars = hts.state_vars | hts.input_vars | hts.output_vars
        
        init = hts.single_init()
        trans = hts.single_trans()
        invar = hts.single_invar()

        init = And(init, invar)
        init_0 = self.at_time(init, 0)
        
        nprop = self.enc.to_nnf(Not(prop))

        self._reset_assertions(self.solver)
        self._add_assertion(self.solver, init_0)
        
        for t in range(1, k+1, 1):
            
            trans_t = self.unroll(trans, invar, t)
            self._add_assertion(self.solver, trans_t)
                
            lb = self.all_simple_loopbacks(relevant_vars, t)

            self._push(self.solver)
            self._push(self.solver)
            
            nprop_k = self.enc.encode(nprop, 0, t)
            self._add_assertion(self.solver, And(nprop_k, Not(Or(lb))))

            if self._solve(self.solver):
                Logger.log("Counterexample (no-loop) found with k=%s"%(t), 1)
                model = self._get_model(self.solver)
                return (t, model)

            nltlprop = []

            self._pop(self.solver)

            for l in range(t+1):
                nprop_l = self.enc.encode_l(nprop, 0, t, l)
                nltlprop.append(And(lb[l], nprop_l))

            self._add_assertion(self.solver, Or(nltlprop))

            if self._solve(self.solver):
                Logger.log("Counterexample (with-loop) found with k=%s"%(t), 1)
                model = self._get_model(self.solver)
                return (t, model)
            else:
                Logger.log("No counterexample found with k=%s"%(t), 1)
                Logger.msg(".", 0, not(Logger.level(1)))

            self._pop(self.solver)
                
        return (k-1, None)
    
