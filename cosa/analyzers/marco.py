#!/usr/bin/env python3
from pysmt.shortcuts import And, BOOL, Implies, Not, Or, Solver, Symbol

# This is a direct translation of the Z3 MARCO demo: https://github.com/Z3Prover/z3/blob/master/examples/python/mus/marco.py
#  which itself is based on
# Enumerating Infeasibility: Finding Multiple MUSes Quickly
# Mark H. Liffiton and Ammar Malik
# in Proc. 10th International Conference on Integration of Artificial Intelligence (AI)
# and Operations Research (OR) techniques in Constraint Programming (CPAIOR-2013), 160-175, May 2013.

# This implementation only enumerates Minimal Unsatisfiable Subsets (MUSes), because that is our interest
# for compositional model checking

class MapSolver:
    def __init__(self, n):
        self.solver = Solver()
        self.n = n
        self.all_n = set(range(n))

    def next_seed(self):
        '''
        Gets the seed from the current model.

        Prefers setting variables to true, which is accomplished by setting all seed values and then
        only removing ones that are in the model.

        E.g. the first call of this function gives a trivial SAT because no literals have been
        added to the model
        '''
        if not self.solver.check_sat():
            return None

        seed = self.all_n.copy()
        model = self.solver.get_model()

        for x, val in model:
            if not val.constant_value():
                seed.remove(int(x.symbol_name()))
        return list(seed)

    def complement(self, aset):
        return self.all_n.difference(aset)

    def block_down(self, frompoint):
        comp = self.complement(frompoint)
        self.solver.add_assertion(Or([Symbol(str(i), BOOL) for i in comp]))

    def block_up(self, frompoint):
        '''
        Blocks all supersets of this current assignment
        '''
        self.solver.add_assertion(Or([Not(Symbol(str(i), BOOL)) for i in frompoint]))

class SubsetSolver:
    def __init__(self, name, hard_constraints, soft_constraints):
        '''
        Takes a solver and a list of soft constraints and can find
        a minimal unsatisfiable subset

        Note: The solver can be in any state/context (it might have assertions already added)
        '''
        self.soft_constraints = soft_constraints
        self.solver = Solver(name=name, unsat_cores_mode='named')
        for c in hard_constraints:
            self.solver.add_assertion(c)
        self.n = len(soft_constraints)
        self.i_var = [Symbol(str(i), BOOL) for i in range(self.n)]
        for i in range(self.n):
            self.solver.add_assertion(Implies(self.i_var[i], soft_constraints[i]))
        self._unsat_core = None

    def to_i_var(self, seed):
        return [self.i_var[i] for i in seed]

    def complement(self, aset):
        return set(range(self.n)).difference(aset)

    def check_subset(self, seed):
        assumptions = self.to_i_var(seed)
        self.solver.push()
        for a in assumptions:
            self.solver.add_assertion(a)
        res = self.solver.check_sat()
        if not res:
            self._unsat_core = self.solver.get_unsat_core()
        self.solver.pop()
        return bool(res)

    def seed_from_core(self):
        seed = list()
        assert self._unsat_core is not None
        core = self._unsat_core
        for x in core:
            if x.is_symbol():
                try:
                    idx = int(x.symbol_name())
                    if idx < self.n:
                        seed.append(idx)
                except ValueError:
                    pass
        return seed

    def shrink(self, seed):
        current = set(seed)
        for i in seed:
            if i not in current:
                continue
            current.remove(i)
            if not self.check_subset(current):
                current = set(self.seed_from_core())
            else:
                current.add(i)
        return list(current)

    def grow(self, seed):
        current = seed
        for i in self.complement(current):
            current.append(i)
            if not self.check_subset(current):
                current.pop()
        return current

def enumerate_sets(csolver, msolver):
    while True:
        seed = msolver.next_seed()
        if seed is None:
            return
        if csolver.check_subset(seed):
            MSS = csolver.grow(seed)
            yield ('MSS', MSS)
            msolver.block_down(MSS)
        else:
            MUS = csolver.shrink(seed)
            yield ('MUS', MUS)
            msolver.block_up(MUS)

def get_mucs(name, hard_constraints, soft_constraints):
    csolver = SubsetSolver(name, hard_constraints, soft_constraints)
    msolver = MapSolver(len(constraints))

    for t, w in enumerate_set(csolver, mcsolver):
        if t == 'MUS':
            yield w

def main():
    a = Symbol('a', BOOL)
    b = Symbol('b', BOOL)
    constraints = [a, Not(a), b, Not(b), Or(a, b)]
    csolver = SubsetSolver(constraints, [])
    msolver = MapSolver(len(constraints))

    for t, w in enumerate_sets(csolver, msolver):
        print(t, w)

if __name__ == "__main__":
    main()
