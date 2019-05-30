from collections import defaultdict
import itertools
from typing import Dict, List, Set, Tuple

from cosa.analyzers.mcsolver import BMCSolver
from cosa.problem import Trace, VerificationStatus
from cosa.utils.formula_mngm import get_free_variables, get_ground_terms
from cosa.utils.logger import Logger

from pysmt.fnode import FNode
# NOTE: Using the substitute from pysmt here
from pysmt.shortcuts import And, EqualsOrIff, Not, Or, simplify, substitute

class CompositionalEngine(BMCSolver):

    def __init__(self, hts, config):
        BMCSolver.__init__(self, hts, config)

    def simple_search(self, properties:List[FNode],
                      bmc_length:int,
                      bmc_length_min:int)->Tuple[str, Trace, int]:
        '''
        Given a list of properties, this method performs a simple search strategy which attempts to prove
        all the properties compositionally.

        This includes both instantiating universally quantified formulae based on the syntax of the properties,
        as well as attempting to determine a suitable total dependency order on properties.
        '''

        solver_name = "compositional"
        solver = self.solver.copy(solver_name)
        self._reset_assertions(solver)
        solver_ind = self.solver.copy("%s_ind"%solver_name)
        self._reset_assertions(solver_ind)

        if bmc_length != 1 or bmc_length_min != 0:
            raise NotImplementedError("Not handling k-induction for k != 1 yet")

        self._init_at_time(self.hts.vars, bmc_length)

        init  = self.hts.single_init()
        trans = self.hts.single_trans()
        invar = self.hts.single_invar()

        if self.config.simplify:
            init  = simplify(init)
            trans = simplify(trans)
            invar = simplify(invar)

        init_0 = self.at_time(And(init, invar), 0)
        Logger.log("Add init and invar", 2)
        self._add_assertion(solver, init_0)

        failed_base = False
        for p in properties:
            nprop0 = Not(self.at_time(p, 0))
            self._push(solver)
            self._add_assertion(solver, nprop0)
            if self._solve(solver):
                Logger.msg("Property violated in initial state", 0)
                failed_base = True
                model = self._get_model(solver)
                model = self._remap_model(self.hts.vars, model, 0)
                trace = self.generate_trace(model, 0, get_free_variables(p))
                return (VerificationStatus.FALSE, trace, 0)
            self._pop(solver)

        assert not failed_base

        Logger.msg("No properties violated in initial state", 1)

        # because these are random, properties over these variables are universally quantified
        universal_variables = self.hts.random_vars
        universal_formulae = dict()
        for p in properties:
            overlap = universal_variables.intersection(get_free_variables(p))
            if overlap:
                universal_formulae[p] = tuple(overlap)

        # TODO: Debug this -- getting counterexamples that violate model invariants
        #       something is not being added as an assertion to the solver correctly

        # try to prove inductively using the other properties
        invar0 = self.at_time(invar, 0)
        self._add_assertion(solver_ind, invar0)
        trans1 = self.unroll(trans, invar, 1)
        self._add_assertion(solver_ind, trans1)


        # can assume all properties in the pre-state
        for prop in properties:
            timed_prop = self.at_time(prop, 0)
            Logger.msg("assuming: " + timed_prop.serialize(100), 2)
            self._add_assertion(solver_ind, timed_prop)

        for num, p in enumerate(properties):
            Logger.msg("Solving property {}: {}".format(num, p.serialize(100)), 1)
            self._push(solver_ind)

            # add heuristic instantiations
            instantiations = self.heuristic_instantiation(universal_formulae, p)
            for i in instantiations:
                timed_inst = self.at_time(i, 0)
                Logger.msg('assuming instantiation: ' + timed_inst.serialize(100), 2)
                self._add_assertion(solver_ind, timed_inst)

            self._add_assertion(solver_ind, self.at_time(Not(p), 1))

            if self._solve(solver_ind):
                Logger.msg("Property violated in inductive step", 1)
                model = self._get_model(solver_ind)
                model = self._remap_model(self.hts.vars, model, 1)
                trace = self.generate_trace(model, 1, get_free_variables(p))
                return (VerificationStatus.UNK, trace, 1)

            self._pop(solver_ind)

            # property was proven, we can add it to the post-state
            self._add_assertion(solver_ind, self.at_time(p, 1))
            Logger.msg("p", 0, not(Logger.level(1)))
            Logger.msg("assuming property in post-state: " + self.at_time(p, 1).serialize(100), 2)

        return (VerificationStatus.TRUE, None, bmc_length)


    def heuristic_instantiation(self, universal_assumptions:Dict[FNode, Tuple[FNode]],
                                prop:FNode)->List[FNode]:
        '''
        Attempts to instantiate universally quantified formulae, guided by
          the syntax of the provided property (which we are currently trying to prove)

        This is heuristic and entirely syntactic.

        It also checks that prop is not the formula being instantiated.

        INPUTS:
           universal_assumptions: a dictionary from universally quantified formulae to their universal variables
           prop: the property which we want to instantiate formulas for
        '''

        # TODO: Figure out how this works if there are other free variables in the formula
        #       i.e. ones that aren't universally quantified

        instantiated_formulae = []

        for formula, univ_vars in universal_assumptions.items():
            if formula == prop:
                continue

            types2idx = defaultdict(set)
            for i, s in enumerate(univ_vars):
                assert s.is_symbol()
                types2idx[s.symbol_type()].add(i)

            matching_symbols = [None]*len(univ_vars)
            for t, idxs in types2idx.items():
                matches = tuple(s for s in get_ground_terms(prop) if s.get_type() == t)
                for i in idxs:
                    matching_symbols[i] = matches

            for instvars in itertools.product(*matching_symbols):
                d = {
                    i:u for i, u in zip(univ_vars, instvars)
                }
                instantiated_formulae.append(substitute(formula, d))

        return instantiated_formulae
