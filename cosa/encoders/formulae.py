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

from pysmt.fnode import FNode
from pysmt.parsing import parse, HRParser, HRLexer, PrattParser, Rule, UnaryOpAdapter, InfixOpAdapter, FunctionCallAdapter
from cosa.representation import TS
from cosa.utils.formula_mngm import get_free_variables
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import quote_names
from cosa.encoders.factory import SyntacticSugarFactory

class ExtLexer(HRLexer):
    def __init__(self, env=None):
        HRLexer.__init__(self, env=env)
        self.rules.insert(0, Rule(r"(!=)", InfixOpAdapter(self.NEquals, 60), False))
        self.rules.insert(0, Rule(r"(prev)", FunctionCallAdapter(self.Prev, 100), False))
        self.rules.insert(0, Rule(r"(next)", FunctionCallAdapter(self.Next, 100), False))

        SyntacticSugarFactory.init_sugar(None)

        for sugar in SyntacticSugarFactory.get_sugars():
            sugar.insert_lexer_rule(self.rules)

        self.compile()

    def Next(self, x):
        return TS.to_next(x)

    def Prev(self, x):
        return TS.to_prev(x)

    def NEquals(self, l, r):
        return self.mgr.Not(self.mgr.Equals(l, r))

def HRParser(env=None):
    return PrattParser(ExtLexer, env=env)

class StringParser(object):

    def __init__(self, encoder_config=None):
        SyntacticSugarFactory.init_sugar(encoder_config)

    def parse_string(self, string):
        return HRParser().parse(string)

    def remap_or2an(self, literal):
        return literal

    def parse_formula(self, strformula, quote=True):
        if strformula is None:
            return None

        if quote:
            strformula = quote_names(strformula)

        return self.parse_string(strformula)

    def parse_formulae(self, str_or_fnodes):
        formulae = []

        if str_or_fnodes is None:
            return formulae

        for s in str_or_fnodes:
            if isinstance(s, str):
                if ('#' in s) or len(s) == 0:
                    continue
                formula = self.parse_formula(s)
            else:
                formula = s
            formula_fv = get_free_variables(formula)
            nextvars = [v for v in formula_fv if TS.is_prime(v)] != []
            prevvars = [v for v in formula_fv if TS.is_prev(v)] != []
            formulae.append((str(s), formula, (nextvars, prevvars)))

        return formulae
