# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, And, get_type, BV, EqualsOrIff
from pysmt.parsing import Rule, UnaryOpAdapter
from cosa.utils.logger import Logger
from cosa.representation import TS
from cosa.utils.formula_mngm import KEYWORDS, BV2B, B2BV

class SyntacticSugarFactory(object):
    sugars = []

    # Additional syntactic sugar should be registered here #
    @staticmethod
    def init_sugar():
        SyntacticSugarFactory.register_sugar(Posedge())
        SyntacticSugarFactory.register_sugar(Negedge())
        SyntacticSugarFactory.register_sugar(Change())
        SyntacticSugarFactory.register_sugar(NoChange())

        for name in SyntacticSugarFactory.sugar_names():
            if name not in KEYWORDS:
                KEYWORDS.append(name)
        
    @staticmethod
    def register_sugar(sugar):
        if sugar.get_name() not in dict(SyntacticSugarFactory.sugars):
            SyntacticSugarFactory.sugars.append((sugar.get_name(), sugar))

    @staticmethod
    def sugar_names():
        return [x[0] for x in SyntacticSugarFactory.sugars]
    
    @staticmethod
    def get_sugars():
        return [x[1] for x in SyntacticSugarFactory.sugars]

class SyntacticSugar(object):
    name = "Syntactic Sugar"
    description = "MISSING DESCRIPTION!"

    def __init__(self):
        pass

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def insert_lexer_rule(self, rules):
        rules.insert(0, Rule(r"(%s)"%self.name, self.adapter(), False))

    def adapter(self):
        Logger.error("Adapter not implemented")
        
class Posedge(SyntacticSugar):
    name = "posedge"
    description = "Clock Posedge"

    def adapter(self):
        return UnaryOpAdapter(self.Posedge, 100)

    def Posedge(self, x):
        if get_type(x).is_bool_type():
            return And(Not(x), TS.to_next(x))
        return And(EqualsOrIff(x, BV(0,1)), BV2B(TS.to_next(x)))

class Negedge(SyntacticSugar):
    name = "negedge"
    description = "Clock Negedge"

    def adapter(self):
        return UnaryOpAdapter(self.Negedge, 100)
        
    def Negedge(self, x):
        if get_type(x).is_bool_type():
            return And(x, Not(TS.to_next(x)))
        return And(BV2B(x), EqualsOrIff(TS.to_next(x), BV(0,1)))
    
class Change(SyntacticSugar):
    name = "change"
    description = "Signal Changes"

    def adapter(self):
        return UnaryOpAdapter(self.Change, 100)
    
    def Change(self, x):
        return Not(EqualsOrIff(x), TS.to_next(x))

class NoChange(SyntacticSugar):
    name = "nochange"
    description = "Signal doesn't Change"

    def adapter(self):
        return UnaryOpAdapter(self.NoChange, 100)

    def NoChange(self, x):
        return EqualsOrIff(x, TS.to_next(x))
