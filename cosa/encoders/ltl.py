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

from pyparsing import Literal, Word, nums, alphas, OneOrMore, ZeroOrMore, restOfLine, LineEnd, Combine, White
from pysmt.shortcuts import TRUE, FALSE, And, Or, Symbol, BV, EqualsOrIff, Implies, get_env
from pysmt.typing import BOOL, BVType
from pysmt.parsing import parse, HRParser, HRLexer, PrattParser, Rule, UnaryOpAdapter, InfixOpAdapter

import pysmt.environment
import pysmt.formula

from cosa.representation import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import get_free_variables, substitute
from cosa.problem import VerificationType
from cosa.utils.formula_mngm import quote_names

from pysmt.operators import new_node_type

LTL_X = new_node_type(node_str="LTL_X")
LTL_F = new_node_type(node_str="LTL_F")
LTL_G = new_node_type(node_str="LTL_G")
LTL_U = new_node_type(node_str="LTL_U")
LTL_R = new_node_type(node_str="LTL_R")
LTL_O = new_node_type(node_str="LTL_O")
LTL_H = new_node_type(node_str="LTL_H")
ALL_LTL = (LTL_X, LTL_F, LTL_G, LTL_U, LTL_R, LTL_O, LTL_H)

class FormulaManager(pysmt.formula.FormulaManager):
    """Extension of FormulaManager to handle LTL Operators."""
    def X(self, formula):
        return self.create_node(node_type=LTL_X, args=(formula,))
    
    def F(self, formula):
        return self.create_node(node_type=LTL_F, args=(formula,))

    def G(self, formula):
        return self.create_node(node_type=LTL_G, args=(formula,))

    def U(self, left, right):
        return self.create_node(node_type=LTL_U, args=(left, right))

    def R(self, left, right):
        return self.create_node(node_type=LTL_R, args=(left, right))

    def O(self, formula):
        return self.create_node(node_type=LTL_O, args=(formula,))

    def H(self, formula):
        return self.create_node(node_type=LTL_H, args=(formula,))
    
class LTLLexer(HRLexer):
    def __init__(self, env=None):
        HRLexer.__init__(self, env=env)
        self.rules.insert(0, Rule(r"(!=)", InfixOpAdapter(self.NEquals, 60), False))
        self.rules.insert(0, Rule(r"(X)", UnaryOpAdapter(self.X, 100), False))
        self.rules.insert(0, Rule(r"(F)", UnaryOpAdapter(self.F, 100), False))
        self.rules.insert(0, Rule(r"(G)", UnaryOpAdapter(self.G, 100), False))
        self.rules.insert(0, Rule(r"(U)", InfixOpAdapter(self.U, 100), False))
        self.rules.insert(0, Rule(r"(R)", InfixOpAdapter(self.R, 100), False))
        self.rules.insert(0, Rule(r"(O)", UnaryOpAdapter(self.O, 100), False))
        self.rules.insert(0, Rule(r"(H)", UnaryOpAdapter(self.H, 100), False))
        self.compile()

    def X(self, x):
        return self.mgr.X(x)
    
    def F(self, x):
        return self.mgr.F(x)
    
    def G(self, x):
        return self.mgr.G(x)

    def U(self, l, r):
        return self.mgr.U(l, r)

    def R(self, l, r):
        return self.mgr.R(l, r)

    def O(self, x):
        return self.mgr.O(x)

    def H(self, x):
        return self.mgr.H(x)
    
    def NEquals(self, l, r):
        return self.mgr.Not(self.mgr.Equals(l, r))

    
from pysmt.type_checker import SimpleTypeChecker
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_bool_to_bool, *ALL_LTL)

from pysmt.oracles import FreeVarsOracle
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, *ALL_LTL)


import pysmt.printers
from pysmt.walkers.generic import handles
LTL_TYPE_TO_STR = { LTL_X: "X", LTL_F: "F", LTL_G: "G", LTL_O: "O", LTL_H: "H"}

class HRLTLPrinter(pysmt.printers.HRPrinter):
    def walk_ltl_r(self, formula):
        return self.walk_nary(formula, " R ")

    def walk_ltl_u(self, formula):
        return self.walk_nary(formula, " U ")

    @handles(LTL_X, LTL_F, LTL_G, LTL_O, LTL_H)
    def walk_ltl(self, formula):
        node_type = formula.node_type()
        op_symbol = LTL_TYPE_TO_STR[node_type]
        self.stream.write("(%s " % op_symbol)
        yield formula.arg(0)
        self.stream.write(")")

# EOC HRPrinter

class HRSerializer(pysmt.printers.HRSerializer):
    PrinterClass = HRLTLPrinter

# EOC HRSerialize

from pysmt.walkers import IdentityDagWalker

def walk_ltl_x(self, formula, args, **kwargs): return self.mgr.X(args[0])
def walk_ltl_f(self, formula, args, **kwargs): return self.mgr.F(args[0])
def walk_ltl_g(self, formula, args, **kwargs): return self.mgr.G(args[0])
def walk_ltl_u(self, formula, args, **kwargs): return self.mgr.U(args[0], args[1])
def walk_ltl_r(self, formula, args, **kwargs): return self.mgr.R(args[0], args[1])
def walk_ltl_o(self, formula, args, **kwargs): return self.mgr.O(args[0])
def walk_ltl_h(self, formula, args, **kwargs): return self.mgr.H(args[0])

IdentityDagWalker.set_handler(walk_ltl_x, LTL_X)
IdentityDagWalker.set_handler(walk_ltl_f, LTL_F)
IdentityDagWalker.set_handler(walk_ltl_g, LTL_G)
IdentityDagWalker.set_handler(walk_ltl_u, LTL_U)
IdentityDagWalker.set_handler(walk_ltl_r, LTL_R)
IdentityDagWalker.set_handler(walk_ltl_o, LTL_O)
IdentityDagWalker.set_handler(walk_ltl_h, LTL_H)
# EOC IdentityDagWalker

from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class EnvironmentLTL(Environment):
    """Extension of pySMT environment."""
    FormulaManagerClass = FormulaManager
    HRSerializerClass = HRSerializer

# EOC EnvironmentLTL

def push_env(env=None):
    """Overload push_env to default to the new Environment class."""
    if env is None:
        env = EnvironmentLTL()
    return pysmt_push_env(env=env)

def ltl_reset_env():
    """Overload reset_env to use the new push_env()."""
    pop_env()
    push_env()
    return get_env()

def has_ltl_operators(formula):

    if formula.is_symbol():
        return False

    if formula.is_constant():
        return False

    if formula.node_type() in ALL_LTL:
        return True

    for child in formula.args():
        if has_ltl_operators(child):
            return True

    return False

def verification_type(formula):
    top = formula
    chd1 = formula.args()[0] if len(formula.args()) > 0 else None
    chd2 = None

    if chd1 is not None:
        chd2 = chd1.args()[0] if len(chd1.args()) > 0 else None

    if (top.node_type() == LTL_G) and (not has_ltl_operators(chd1)):
        return (VerificationType.SAFETY, chd1)

    if (top.node_type() == LTL_F) and (not has_ltl_operators(chd1)):
        return (VerificationType.EVENTUALLY, chd1)

    if (top.node_type() == LTL_G) and (chd1.node_type() == LTL_F) and (not has_ltl_operators(chd2)):
        return (VerificationType.LIVENESS, chd2)

    return (VerificationType.LTL, formula)

class LTLEncoder(object):

    def __init__(self):
        self.mgr = get_env().formula_manager
        
    def to_nnf(self, formula):
        if formula.is_constant():
            return formula
        
        if formula.is_symbol():
            return formula

        if formula.is_equals():
            return self.mgr.Equals(self.to_nnf(formula.args()[0]), self.to_nnf(formula.args()[1]))

        if formula.is_and():
            return self.mgr.And(self.to_nnf(formula.args()[0]), self.to_nnf(formula.args()[1]))
        
        if formula.is_implies():
            return self.mgr.Or(self.mgr.Not(self.to_nnf(formula.args()[0])), self.to_nnf(formula.args()[1]))

        if formula.is_or():
            return self.mgr.Or(self.to_nnf(formula.args()[0]), self.to_nnf(formula.args()[1]))
        
        if formula.is_not():
            if formula.args()[0].is_symbol():
                return self.mgr.Not(formula.args()[0])

            if formula.args()[0].node_type() == LTL_X:
                return self.mgr.X(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])))

            if formula.args()[0].node_type() == LTL_F:
                return self.mgr.G(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])))

            if formula.args()[0].node_type() == LTL_G:
                return self.mgr.F(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])))

            if formula.args()[0].node_type() == LTL_U:
                return self.mgr.R(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])), self.to_nnf(self.mgr.Not(formula.args()[0].args()[1])))

            if formula.args()[0].node_type() == LTL_R:
                return self.mgr.U(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])), self.to_nnf(self.mgr.Not(formula.args()[0].args()[1])))

            if formula.args()[0].node_type() == LTL_O:
                return self.mgr.H(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])))

            if formula.args()[0].node_type() == LTL_H:
                return self.mgr.O(self.to_nnf(self.mgr.Not(formula.args()[0].args()[0])))
            
            if formula.args()[0].is_and():
                l = formula.args()[0].args()[0]
                r = formula.args()[0].args()[1]
                return self.mgr.Or(self.to_nnf(self.mgr.Not(l)), self.to_nnf(self.mgr.Not(r)))

            if formula.args()[0].is_or():
                l = formula.args()[0].args()[0]
                r = formula.args()[0].args()[1]
                return self.mgr.And(self.to_nnf(self.mgr.Not(l)), self.to_nnf(self.mgr.Not(r)))

            if formula.args()[0].is_implies():
                l = formula.args()[0].args()[0]
                r = formula.args()[0].args()[1]
                                
                return self.mgr.And(self.to_nnf(l), self.to_nnf(self.mgr.Not(r)))

            
            return self.mgr.Not(self.to_nnf(formula.args()[0]))

        return formula
        
    def encode(self, formula, t_i, t_k):
        if formula.is_constant():
            return formula
        
        if formula.is_symbol():
            assert (t_i >= 0)
            return TS.get_timed(formula, t_i)

        if formula.is_equals():
            return self.mgr.Equals(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))

        if formula.is_and():
            return self.mgr.And(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))

        if formula.is_implies():
            return self.mgr.Or(self.mgr.Not(self.encode(formula.args()[0], t_i, t_k)), self.encode(formula.args()[1], t_i, t_k))
        
        if formula.is_not():
            return self.mgr.Not(self.encode(formula.args()[0], t_i, t_k))

        if formula.is_lt():
            return self.mgr.LT(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))

        if formula.is_bv_ult():
            return self.mgr.BVULT(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))

        if formula.is_bv_ule():
            return self.mgr.BVULE(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))
        
        if formula.is_or():
            return self.mgr.Or(self.encode(formula.args()[0], t_i, t_k), self.encode(formula.args()[1], t_i, t_k))
        
        if formula.node_type() == LTL_X:
            if t_i < t_k:
                return self.encode(formula.args()[0], t_i+1, t_k)
            return FALSE()

        if formula.node_type() == LTL_G:
            return FALSE()

        if formula.node_type() == LTL_F:
            return Or([self.encode(formula.args()[0], j, t_k) for j in range(t_i, t_k+1, 1)])

        if formula.node_type() == LTL_U:
            formula_h = formula.args()[0]
            formula_g = formula.args()[1]
            
            return Or([And(self.encode(formula_g, j, t_k), \
                           And([self.encode(formula_h, n, t_k) for n in range(t_i, j, 1)])) for j in range(t_i, t_k+1, 1)])

        if formula.node_type() == LTL_R:
            formula_h = formula.args()[0]
            formula_g = formula.args()[1]
            
            return Or([And(self.encode(formula_h, j, t_k), \
                           And([self.encode(formula_g, n, t_k) for n in range(t_i, j+1, 1)])) for j in range(t_i, t_k+1, 1)])

        if formula.node_type() == LTL_O:
            return Or([self.encode(formula.args()[0], j, t_k) for j in range(t_i, t_k+1, 1)])

        if formula.node_type() == LTL_H:
            return And([self.encode(formula.args()[0], j, t_k) for j in range(t_i, t_k+1, 1)])
        

        Logger.error("Invalid LTL operator")
        
    def encode_l(self, formula, t_i, t_k, t_l):

        if formula.is_constant():
            return formula
        
        if formula.is_symbol():
            assert (t_i >= 0)
            return TS.get_timed(formula, t_i)

        if formula.is_equals():
            return self.mgr.Equals(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))

        if formula.is_and():
            return self.mgr.And(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))

        if formula.is_or():
            return self.mgr.Or(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))

        if formula.is_lt():
            return self.mgr.LT(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))

        if formula.is_bv_ult():
            return self.mgr.BVULT(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))

        if formula.is_bv_ule():
            return self.mgr.BVULE(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))
        
        if formula.is_implies():
            return self.mgr.Implies(self.encode_l(formula.args()[0], t_i, t_k, t_l), self.encode_l(formula.args()[1], t_i, t_k, t_l))
        
        if formula.is_not():
            return self.mgr.Not(self.encode_l(formula.args()[0], t_i, t_k, t_l))
        
        if formula.node_type() == LTL_X:
            if t_i < t_k:
                return self.encode_l(formula.args()[0], t_i+1, t_k, t_l)
            return self.encode_l(formula.args()[0], t_l, t_k, t_l)

        if formula.node_type() == LTL_G:
            return And([self.encode_l(formula.args()[0], j, t_k, t_l) for j in range(min(t_i, t_l), t_k+1, 1)])

        if formula.node_type() == LTL_F:
            return Or([self.encode_l(formula.args()[0], j, t_k, t_l) for j in range(min(t_i, t_l), t_k+1, 1)])

        if formula.node_type() == LTL_U:
            formula_h = formula.args()[0]
            formula_g = formula.args()[1]
            
            u1 = Or([And(self.encode_l(formula_g, j, t_k, t_l), \
                         And([self.encode_l(formula_h, n, t_k, t_l) for n in range(t_i, j, 1)])) for j in range(t_i, t_k+1, 1)])
        
            u2 = Or([And(self.encode_l(formula_g, j, t_k, t_l), \
                         And([self.encode_l(formula_h, n, t_k, t_l) for n in range(t_i, t_k+1, 1)]), \
                         And([self.encode_l(formula_h, n, t_k, t_l) for n in range(t_l, j, 1)])) for j in range(t_l, t_i, 1)])

            return Or(u1, u2)

        if formula.node_type() == LTL_R:
            formula_h = formula.args()[0]
            formula_g = formula.args()[1]
            
            r1 = And([self.encode_l(formula_g, j, t_k, t_l) for j in range(min(t_i, t_l), t_k+1, 1)])
            
            r2 = Or([And(self.encode_l(formula_h, j, t_k, t_l), \
                         And([self.encode_l(formula_g, n, t_k, t_l) for n in range(t_i, j+1, 1)])) for j in range(t_i, t_k+1, 1)])
        
            r3 = Or([And(self.encode_l(formula_h, j, t_k, t_l), \
                         And([self.encode_l(formula_g, n, t_k, t_l) for n in range(t_i, t_k+1, 1)]), \
                         And([self.encode_l(formula_g, n, t_k, t_l) for n in range(t_l, j+1, 1)])) for j in range(t_l, t_i, 1)])

            return Or(r1, r2, r3)

        if formula.node_type() == LTL_O:
            return Or([self.encode_l(formula.args()[0], j, t_k, t_l) for j in range(t_i, t_k+1, 1)])

        if formula.node_type() == LTL_H:
            return And([self.encode_l(formula.args()[0], j, t_k, t_l) for j in range(t_i, t_k+1, 1)])
        
        Logger.error("Invalid LTL operator")


class LTLParser(object):

    def __init__(self):
        pass
    
    def parse_string(self, string):
        return PrattParser(LTLLexer).parse(string)

    def remap_or2an(self, literal):
        return literal
    
    def parse_formula(self, strformula):
        if strformula is None:
            return None
        return self.parse_string(quote_names(strformula))

    def parse_formulae(self, strforms):
        formulae = []

        if strforms is None:
            return formulae

        for strform in strforms:
            if ("#" not in strform) and (strform != ""):
                formula = self.parse_formula(strform)
                formula_fv = get_free_variables(formula)
                nextvars = [v for v in formula_fv if TS.is_prime(v)] != []
                prevvars = [v for v in formula_fv if TS.is_prev(v)] != []
                formulae.append((strform, formula, (nextvars, prevvars)))

        return formulae

