# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.utils.formula_mngm import KEYWORDS
from cosa.utils.logger import Logger

class SyntacticSugarFactory(object):
    sugars = []

    # Additional syntactic sugar should be registered here #
    @staticmethod
    def init_sugar():
        from cosa.encoders.sugar import Posedge, Negedge, Change, NoChange, MemAccess, Ones, Zero
    
        SyntacticSugarFactory.register_sugar(MemAccess())
        SyntacticSugarFactory.register_sugar(Posedge())
        SyntacticSugarFactory.register_sugar(Negedge())
        SyntacticSugarFactory.register_sugar(Change())
        SyntacticSugarFactory.register_sugar(NoChange())
        SyntacticSugarFactory.register_sugar(Ones())
        SyntacticSugarFactory.register_sugar(Zero())

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
    
        
class ModelParsersFactory(object):
    parsers = []

    # Additional parsers should be registered here #
    @staticmethod
    def init_parsers():
        from cosa.encoders.symbolic_transition_system import SymbolicTSParser, SymbolicSimpleTSParser
        from cosa.encoders.explicit_transition_system import ExplicitTSParser
        from cosa.encoders.btor2 import BTOR2Parser
        from cosa.encoders.coreir import CoreIRParser
        from cosa.encoders.verilog_yosys import VerilogYosysParser
        from cosa.encoders.verilog_hts import VerilogHTSParser
        
        ModelParsersFactory.register_parser(CoreIRParser())
        ModelParsersFactory.register_parser(SymbolicTSParser())
        ModelParsersFactory.register_parser(SymbolicSimpleTSParser())
        ModelParsersFactory.register_parser(ExplicitTSParser())
        ModelParsersFactory.register_parser(BTOR2Parser())
        # ModelParsersFactory.register_parser(VerilogYosysParser())
        ModelParsersFactory.register_parser(VerilogHTSParser())
        
    @staticmethod
    def register_parser(parser):
        if parser.get_name() not in dict(ModelParsersFactory.parsers):
            if parser.is_available():
                ModelParsersFactory.parsers.append((parser.get_name(), parser))

    @staticmethod
    def parser_by_name(name):
        ModelParsersFactory.init_parsers()
        dprint = dict(ModelParsersFactory.parsers)
        if name not in dprint:
            Logger.error("Parser \"%s\" is not registered"%name)
        return dprint[name]

    @staticmethod
    def get_parsers():
        ModelParsersFactory.init_parsers()
        return [x[1] for x in ModelParsersFactory.parsers]

class GeneratorsFactory(object):
    generators = []

    # Additional generators should be registered here #
    @staticmethod
    def init_generators():
        from cosa.encoders.generators import ScoreBoardGenerator, RandomGenerator
        
        GeneratorsFactory.register_generator(ScoreBoardGenerator())
        GeneratorsFactory.register_generator(RandomGenerator())

    @staticmethod
    def register_generator(generator):
        if generator.get_name() not in dict(GeneratorsFactory.generators):
            GeneratorsFactory.generators.append((generator.get_name(), generator))

    @staticmethod
    def generator_by_name(name):
        GeneratorsFactory.init_generators()
        dgenerator = dict(GeneratorsFactory.generators)
        if name not in dgenerator:
            Logger.error("Generator \"%s\" is not registered"%name)
        return dgenerator[name]

    @staticmethod
    def get_generators():
        GeneratorsFactory.init_generators()
        return [x[1] for x in GeneratorsFactory.generators]
