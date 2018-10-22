# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# This module implements the BMC-based techniques described in
# "Efficient Anytime Techniques for Model-Based Safety Analysis" by
# M. Bozzano, A. Cimatti, A. Griggio, and C. Mattarei.

from pysmt.shortcuts import And, Or, Solver, TRUE, FALSE, Not, EqualsOrIff, Implies, Iff, Symbol, BOOL, simplify
from pysmt.typing import BOOL, BVType, ArrayType
from pysmt.rewritings import disjunctive_partition, conjunctive_partition

from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables, SortingNetwork
from cosa.representation import TS, HTS

from cosa.problem import VerificationStatus
from cosa.analyzers.mcsolver import TraceSolver, BMCSolver, VerificationStrategy
from cosa.analyzers.bmc_safety import BMCSafety

NL = "\n"

class BMCParametric(BMCSafety):

    hts = None
    config = None

    TraceID = 0

    total_time = 0.0
    tracefile = None

    region = None
    models = None
    cs_count = -1
    
    def _get_param_assignments(self, model, time, parameters, monotonic=True):
        p_ass = []

        fwd = False
        
        for p in parameters:
            p_time = model[TS.get_ptimed(p, 0)]
            if p.symbol_type() == BOOL:
                if monotonic:
                    if p_time == TRUE():
                        p_ass.append(p)
                else:
                    p_ass.append(p if p_time == TRUE() else Not(p))
            else:
                p_ass.append(EqualsOrIff(p, p_time))

        p_ass = And(p_ass)
        self.region = simplify(Or(self.region, p_ass))

        if self.models is None:
            self.models = []
        self.models.append((model, time))

        Logger.msg("+", 0, not(Logger.level(1)))
        self.cs_count += 1
        Logger.log("Found assignment \"%s\""%(p_ass.serialize(threshold=100)), 1)

        return (p_ass, False)

    def parametric_safety(self, prop, k_max, k_min, parameters, monotonic=True, at_most=-1):
        if len(parameters) == 0:
            Logger.error("Parameters size cannot be 0")
        
        lemmas = self.hts.lemmas
        self._init_at_time(self.hts.vars, k_max)

        monotonic = True

        # if monotonic:
        #     for p in parameters:
        #         self.set_preferred((p, False))
        
        self.region = FALSE()

        generalize = lambda model, t: self._get_param_assignments(model, t, parameters, monotonic)

        if at_most == -1:
            cardinality = len(parameters)
        else:
            cardinality = at_most

        prev_cs_count = 0

        prove = self.config.prove

        step = 5
        same_res_counter = 0
        k = step
        end = False
        has_next = TS.has_next(prop)


        # Strategy selection
        increase_k = False
        
        if cardinality == -2:
            (t, status) = self.solve_safety_inc_fwd(self.hts, prop, k_max, k_min, all_vars=False, generalize=generalize)
        else:
            sn = SortingNetwork.sorting_network(parameters)

            if increase_k:
                # Approach with incremental increase of bmc k
                while k < k_max+1:
                    for at in range(cardinality):
                        Logger.msg("[%d,%d]"%((at+1), k), 0, not(Logger.level(1)))
                        
                        sn_k = sn[at+1] if at+1 < len(sn) else FALSE()
                        bound_constr = Or(sn_k, self.region)
                        bound_constr = bound_constr if not has_next else Or(bound_constr, TS.to_next(bound_constr))
                        
                        self.config.prove = False
                        (t, status) = self.solve_safety_inc_bwd(self.hts, Or(prop, bound_constr), k, generalize=generalize)

                        if (prev_cs_count == self.cs_count):
                            same_res_counter += 1
                        else:
                            same_res_counter = 0

                        prev_cs_count = self.cs_count

                        if (prove == True) and ((same_res_counter > 1) or (at == cardinality-1)): 
                            Logger.msg("[>%d,%d]"%((at+1), k), 0, not(Logger.level(1)))

                            if (at_most > -1) and (at_most < cardinality):
                                sn_k = sn[at_most-1]
                            else:
                                sn_k = FALSE()
                            bound_constr = Or(sn_k, self.region)
                            bound_constr = bound_constr if not has_next else Or(bound_constr, TS.to_next(bound_constr))
                            
                            self.config.prove = True
                            (t, status) = self.solve_safety(self.hts, Or(prop, bound_constr), k, max(k_min, k-step))

                            if status == True:
                                end = True
                                break

                        if (same_res_counter > 2) and (k < k_max):
                            break

                    if end:
                        break
                    k += step
            else:
                # Approach with fixed bmc k
                for at in range(cardinality):
                    Logger.msg("[%d]"%((at+1)), 0, not(Logger.level(1)))
                    
                    sn_k = sn[at+1] if at+1 < len(sn) else FALSE()
                    bound_constr = Or(sn_k, self.region)
                    bound_constr = bound_constr if not has_next else Or(bound_constr, TS.to_next(bound_constr))
                    
                    self.config.prove = False
                    (t, status) = self.solve_safety_inc_bwd(self.hts, Or(prop, bound_constr), k_max, generalize=generalize)
                    
                    if simplify(self.region) == TRUE():
                        break
                    
                    if (prev_cs_count == self.cs_count):
                        same_res_counter += 1
                    else:
                        same_res_counter = 0

                    prev_cs_count = self.cs_count

                    if (prove == True) and ((same_res_counter > 1) or (at == cardinality-1)):
                        Logger.msg("[>%d]"%((at+1)), 0, not(Logger.level(1)))
                        
                        if (at_most > -1) and (at_most < cardinality):
                            sn_k = sn[at_most-1]
                        else:
                            sn_k = FALSE()
                        bound_constr = Or(sn_k, self.region)
                        bound_constr = bound_constr if not has_next else Or(bound_constr, TS.to_next(bound_constr))
                        
                        self.config.prove = True
                        (t, status) = self.solve_safety(self.hts, Or(prop, bound_constr), k_max, k_min)
                        if status == True:
                            break
        
        traces = None
        if (self.models is not None) and (simplify(self.region) not in [TRUE(), FALSE()]):
            traces = []
            for (model, time) in self.models:
                model = self._remap_model(self.hts.vars, model, time)
                trace = self.generate_trace(model, time, get_free_variables(prop))
                traces.append(trace)

        region = []
        dass = {}

        # Sorting result by size
        for ass in list(disjunctive_partition(self.region)):
            cp = list(conjunctive_partition(ass))
            size = len(cp)
            if size not in dass:
                dass[size] = []
            dass[size].append(ass)

        indexes = list(dass.keys())
        indexes.sort()
        for size in indexes:
            region += dass[size]
                
        if status == True:
            return (VerificationStatus.TRUE, traces, region)
        elif status is not None:
            return (VerificationStatus.FALSE, traces, region)
        else:
            return (VerificationStatus.UNK, traces, region)
