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

from pysmt.shortcuts import TRUE, FALSE, And, Or, Symbol, BV, EqualsOrIff, Implies, get_env
from pysmt.typing import BOOL, BVType
from pysmt.parsing import parse, HRParser, HRLexer, PrattParser, Rule, UnaryOpAdapter, InfixOpAdapter

import pysmt.environment
import pysmt.formula

from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger

from pysmt.operators import new_node_type

LTL_X = new_node_type(node_str="LTL_X")
LTL_F = new_node_type(node_str="LTL_F")
LTL_G = new_node_type(node_str="LTL_G")
LTL_U = new_node_type(node_str="LTL_U")
LTL_R = new_node_type(node_str="LTL_R")
LTL_O = new_node_type(node_str="LTL_O")
LTL_H = new_node_type(node_str="LTL_H")
ALL_LTL = (LTL_X, LTL_F, LTL_G, LTL_U, LTL_R, LTL_O, LTL_H)

ASSIGN = new_node_type(node_str="ASSIGN")
DEFINE = new_node_type(node_str="DEFINE")

def Assign(left, right):
    return get_env().formula_manager.Assign(left, right)

def Define(left, right):
    return get_env().formula_manager.Define(left, right)

def Finally(arg):
    return get_env().formula_manager.F(arg)

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

    def Assign(self, left, right):
        return self.create_node(node_type=ASSIGN, args=(left, right), payload=(1,))

    def Define(self, left, right):
        return self.create_node(node_type=DEFINE, args=(left, right), payload=(1,))
    
class ExtLexer(HRLexer):
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
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_bv_to_bool, ASSIGN)
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_bv_to_bool, DEFINE)

from pysmt.oracles import FreeVarsOracle
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, *ALL_LTL)
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, ASSIGN)
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, DEFINE)

import pysmt.printers
from pysmt.walkers.generic import handles
LTL_TYPE_TO_STR = { LTL_X: "X", LTL_F: "F", LTL_G: "G", LTL_O: "O", LTL_H: "H"}

class ExtHRPrinter(pysmt.printers.HRPrinter):
    def walk_ltl_r(self, formula):
        return self.walk_nary(formula, " R ")

    def walk_ltl_u(self, formula):
        return self.walk_nary(formula, " U ")

    def walk_assign(self, formula):
        return self.walk_nary(formula, " <= ")

    def walk_define(self, formula):
        return self.walk_nary(formula, " = ")
    
    @handles(LTL_X, LTL_F, LTL_G, LTL_O, LTL_H)
    def walk_ltl(self, formula):
        node_type = formula.node_type()
        op_symbol = LTL_TYPE_TO_STR[node_type]
        self.stream.write("(%s " % op_symbol)
        yield formula.arg(0)
        self.stream.write(")")

# EOC HRPrinter

class HRSerializer(pysmt.printers.HRSerializer):
    PrinterClass = ExtHRPrinter

# EOC HRSerialize

from pysmt.walkers import IdentityDagWalker

def walk_ltl_x(self, formula, args, **kwargs): return self.mgr.X(args[0])
def walk_ltl_f(self, formula, args, **kwargs): return self.mgr.F(args[0])
def walk_ltl_g(self, formula, args, **kwargs): return self.mgr.G(args[0])
def walk_ltl_u(self, formula, args, **kwargs): return self.mgr.U(args[0], args[1])
def walk_ltl_r(self, formula, args, **kwargs): return self.mgr.R(args[0], args[1])
def walk_ltl_o(self, formula, args, **kwargs): return self.mgr.O(args[0])
def walk_ltl_h(self, formula, args, **kwargs): return self.mgr.H(args[0])

def walk_assign(self, formula, args, **kwargs): return self.mgr.Assign(args[0], args[1])
def walk_define(self, formula, args, **kwargs): return self.mgr.Define(args[0], args[1])

IdentityDagWalker.set_handler(walk_ltl_x, LTL_X)
IdentityDagWalker.set_handler(walk_ltl_f, LTL_F)
IdentityDagWalker.set_handler(walk_ltl_g, LTL_G)
IdentityDagWalker.set_handler(walk_ltl_u, LTL_U)
IdentityDagWalker.set_handler(walk_ltl_r, LTL_R)
IdentityDagWalker.set_handler(walk_ltl_o, LTL_O)
IdentityDagWalker.set_handler(walk_ltl_h, LTL_H)

IdentityDagWalker.set_handler(walk_assign, ASSIGN)
IdentityDagWalker.set_handler(walk_define, DEFINE)

def walk_simplify_assign(self, formula, args, **kwargs):
    assert len(args) == 2

    sl = args[0]
    sr = args[1]

    if sl.is_constant() and sr.is_constant():
        l = sl.constant_value()
        r = sr.constant_value()
        return self.manager.Bool(l == r)
    elif sl == sr:
        return self.manager.TRUE()
    else:
        return self.manager.Assign(sl, sr)

def walk_simplify_define(self, formula, args, **kwargs):
    assert len(args) == 2

    sl = args[0]
    sr = args[1]

    if sl.is_constant() and sr.is_constant():
        l = sl.constant_value()
        r = sr.constant_value()
        return self.manager.Bool(l == r)
    elif sl == sr:
        return self.manager.TRUE()
    else:
        return self.manager.Define(sl, sr)
    
from pysmt.simplifier import Simplifier
Simplifier.set_handler(walk_simplify_assign, ASSIGN)
Simplifier.set_handler(walk_simplify_define, DEFINE)

# EOC IdentityDagWalker

from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class CosaEnvironment(Environment):
    """Extension of pySMT environment."""
    FormulaManagerClass = FormulaManager
    HRSerializerClass = HRSerializer

# EOC EnvironmentLTL

def push_env(env=None):
    """Overload push_env to default to the new Environment class."""
    if env is None:
        env = CosaEnvironment()
    return pysmt_push_env(env=env)

def reset_env():
    """Overload reset_env to use the new push_env()."""
    pop_env()
    push_env()
    return get_env()


