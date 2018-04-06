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

from pysmt.parsing import parse, HRParser, HRLexer, PrattParser, Rule, UnaryOpAdapter, InfixOpAdapter
from cosa.util.logger import Logger
from cosa.core.transition_system import TS

KEYWORDS = ["not","False","True","next","prev"]
OPERATORS = [(" < "," u< "), \
             (" > "," u> "), \
             (" >= "," u>= "), \
             (" <= "," u<= ")]

class ExtLexer(HRLexer):
    def __init__(self, env=None):
        HRLexer.__init__(self, env=env)
        self.rules.insert(0, Rule(r"(!=)", InfixOpAdapter(self.NEquals, 60), False))
        self.rules.insert(0, Rule(r"(next)", UnaryOpAdapter(self.Next, 50), False))
        self.rules.insert(0, Rule(r"(prev)", UnaryOpAdapter(self.Prev, 50), False))
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

    def __init__(self):
        pass
    
    def parse_string(self, string):
        return HRParser().parse(string)

    def remap_or2an(self, literal):
        return literal
    
    def parse_formula(self, strformula):
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

        for strform in strforms:
            if ("#" not in strform) and (strform != ""):
                formulae.append((strform, self.parse_formula(strform)))
            # try:
            #     if ("#" not in strform) and (strform != ""):
            #         formulae.append((strform, self.parse_formula(strform)))
            # except Exception as e:
            #     Logger.error(str(e))

        return formulae

    
