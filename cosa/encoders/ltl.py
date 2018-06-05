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

from cosa.transition_systems import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import get_free_variables, substitute


from pysmt.operators import new_node_type

KEYWORDS = ["not","False","True","next","prev","G","F","X","U","R"]
OPERATORS = [(" < "," u< "), \
             (" > "," u> "), \
             (" >= "," u>= "), \
             (" <= "," u<= ")]

LTL_X = new_node_type(node_str="LTL_X")
LTL_Y = new_node_type(node_str="LTL_Y")
LTL_Z = new_node_type(node_str="LTL_Z")
LTL_F = new_node_type(node_str="LTL_F")
LTL_G = new_node_type(node_str="LTL_G")
LTL_O = new_node_type(node_str="LTL_O")
LTL_H = new_node_type(node_str="LTL_H")
LTL_U = new_node_type(node_str="LTL_U")
LTL_R = new_node_type(node_str="LTL_R")
ALL_LTL = (LTL_X, LTL_Y, LTL_Z,
           LTL_F, LTL_G, LTL_O, LTL_H,
           LTL_U, LTL_R)

class FormulaManager(pysmt.formula.FormulaManager):
    """Extension of FormulaManager to handle LTL Operators."""
    def X(self, formula):
        return self.create_node(node_type=LTL_X, args=(formula,))

    def Y(self, formula):
        return self.create_node(node_type=LTL_Y, args=(formula,))

    def Z(self, formula):
        return self.create_node(node_type=LTL_Z, args=(formula,))

    def F(self, formula):
        return self.create_node(node_type=LTL_F, args=(formula,))

    def G(self, formula):
        return self.create_node(node_type=LTL_G, args=(formula,))

    def O(self, formula):
        return self.create_node(node_type=LTL_O, args=(formula,))

    def H(self, formula):
        return self.create_node(node_type=LTL_H, args=(formula,))

    def S(self, left, right):
        return self.create_node(node_type=LTL_R, args=(left, right))

    def U(self, left, right):
        return self.create_node(node_type=LTL_U, args=(left, right))

    # We can also add syntactic sugar, by creating constructors that
    # are not mapped directly to a new node type. For example X^n:
    def Xn(self, n, formula):
        X_ = self.X
        res = formula
        for _ in range(n):
            res = X_(res)
        return res


class LTLLexer(HRLexer):
    def __init__(self, env=None):
        HRLexer.__init__(self, env=env)
        self.rules.insert(0, Rule(r"(!=)", InfixOpAdapter(self.NEquals, 60), False))
        self.rules.insert(0, Rule(r"(X)", UnaryOpAdapter(self.X, 100), False))
        self.rules.insert(0, Rule(r"(Y)", UnaryOpAdapter(self.Y, 100), False))
        self.rules.insert(0, Rule(r"(Z)", UnaryOpAdapter(self.Z, 100), False))
        self.rules.insert(0, Rule(r"(G)", UnaryOpAdapter(self.G, 100), False))
        self.rules.insert(0, Rule(r"(F)", UnaryOpAdapter(self.F, 100), False))
        self.rules.insert(0, Rule(r"(H)", UnaryOpAdapter(self.H, 100), False))
        self.rules.insert(0, Rule(r"(O)", UnaryOpAdapter(self.O, 100), False))
        self.rules.insert(0, Rule(r"(U)", InfixOpAdapter(self.U, 100), False))
        self.rules.insert(0, Rule(r"(R)", InfixOpAdapter(self.R, 100), False))
        self.compile()

    def X(self, x):
        return self.mgr.X(x)

    def Y(self, x):
        return self.mgr.Y(x)

    def Z(self, x):
        return self.mgr.Z(x)
    
    def G(self, x):
        return self.mgr.G(x)

    def O(self, x):
        return self.mgr.O(x)

    def H(self, x):
        return self.mgr.H(x)
    
    def F(self, x):
        return self.mgr.F(x)

    def U(self, l, r):
        return self.mgr.U(l, r)

    def R(self, l, r):
        return self.mgr.R(l, r)
    
    def NEquals(self, l, r):
        return self.mgr.Not(self.mgr.Equals(l, r))

    
#
# For the system to work, we need to extend a few walkers.
#

# The first extension is the TypeChecker. The typechecker provides
# several convenience methods for many types of operators. In this
# case, all the LTL operators have boolean argument and boolean return
# value, therefore we map them all to walk_bool_to_bool.
#
# This is an example of how to extend an existing class
# (SimpleTypeChecker) in order to deal with new node-types, by calling
# an existing method (walk_bool_to_bool).
from pysmt.type_checker import SimpleTypeChecker
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_bool_to_bool, *ALL_LTL)

from pysmt.oracles import FreeVarsOracle
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, *ALL_LTL)

# An alternative approach is to subclass the walker that we are
# interested in. For example, the HRPrinter has utility methods for
# the nary operators. For the unary operators, we define a unique
# function.  The walk_* method that we override needs to have the same
# name as the string used in new_node_type (lowercase): for LTL_G, we
# override walk_ltl_g.

import pysmt.printers
from pysmt.walkers.generic import handles
LTL_TYPE_TO_STR = { LTL_X: "X", LTL_Y: "Y", LTL_Z: "Z",
                    LTL_F: "F", LTL_G: "G", LTL_O: "O", LTL_H: "H"}

class HRPrinter(pysmt.printers.HRPrinter):
    def walk_ltl_r(self, formula):
        return self.walk_nary(formula, " R ")

    def walk_ltl_u(self, formula):
        return self.walk_nary(formula, " U ")

    @handles(LTL_X, LTL_Y, LTL_Z, LTL_F, LTL_G, LTL_O, LTL_H)
    def walk_ltl(self, formula):
        node_type = formula.node_type()
        op_symbol = LTL_TYPE_TO_STR[node_type]
        self.stream.write("(%s " % op_symbol)
        yield formula.arg(0)
        self.stream.write(")")

# EOC HRPrinter

class HRSerializer(pysmt.printers.HRSerializer):
    PrinterClass = HRPrinter

# EOC HRSerialize

# Finally, a third option is to define new methods and attach them to
# existing classes. We do so for the IdentityDagWalker
from pysmt.walkers import IdentityDagWalker

def walk_ltl_x(self, formula, args, **kwargs): return self.mgr.X(args[0])
def walk_ltl_y(self, formula, args, **kwargs): return self.mgr.Y(args[0])
def walk_ltl_u(self, formula, args, **kwargs): return self.mgr.U(args[0], args[1])
def walk_ltl_r(self, formula, args, **kwargs): return self.mgr.S(args[0], args[1])
def walk_ltl_f(self, formula, args, **kwargs): return self.mgr.F(args[0])
def walk_ltl_g(self, formula, args, **kwargs): return self.mgr.G(args[0])
def walk_ltl_o(self, formula, args, **kwargs): return self.mgr.O(args[0])
def walk_ltl_h(self, formula, args, **kwargs): return self.mgr.H(args[0])

IdentityDagWalker.set_handler(walk_ltl_x, LTL_X)
IdentityDagWalker.set_handler(walk_ltl_y, LTL_Y)
IdentityDagWalker.set_handler(walk_ltl_u, LTL_U)
IdentityDagWalker.set_handler(walk_ltl_r, LTL_R)
IdentityDagWalker.set_handler(walk_ltl_f, LTL_F)
IdentityDagWalker.set_handler(walk_ltl_g, LTL_G)
IdentityDagWalker.set_handler(walk_ltl_o, LTL_O)
IdentityDagWalker.set_handler(walk_ltl_h, LTL_H)
# EOC IdentityDagWalker

from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class EnvironmentLTL(Environment):
    """Extension of pySMT environment."""
    # Only specify new classes. Classes that have been extended
    # directly do not need to be redefined here (e.g., TypeChecker)
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


        print(formula)
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
        
        formula = strformula.replace("\\","")
        for lit in set(re.findall("([a-zA-Z][a-zA-Z_$\.0-9]*)+", formula)):
            if lit in KEYWORDS:
                continue
            formula = formula.replace(lit, "\'%s\'"%self.remap_or2an(lit))
        for op in OPERATORS:
            formula = formula.replace(op[0], op[1])
        return self.parse_string(formula)

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

