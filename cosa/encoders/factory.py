# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os
import shutil

from cosa.utils.formula_mngm import KEYWORDS
from cosa.utils.generic import suppress_output, restore_output
from cosa.utils.logger import Logger


def available(toolname, optiongrep=None):
    if shutil.which(toolname) is None:
        return False

    print_level = 3
    if not Logger.level(print_level):
        saved_status = suppress_output()

    # assuming there's a -h for the program
    # yosys and verific have it
    retval = os.system("{} -h".format(toolname))

    if not Logger.level(print_level):
        restore_output(saved_status)

    if optiongrep is not None:
        with open(saved_status[0].name, 'r') as f:
            output = f.read()
            if optiongrep not in output:
                return False

    return (retval == 0)

class SyntacticSugarFactory(object):
    sugars = []

    # Additional syntactic sugar should be registered here #
    @staticmethod
    def init_sugar(encoder_config):
        from cosa.encoders.sugar import Posedge, Negedge, Change, NoChange, MemAccess, Ones, Zero, Dec2BV

        SyntacticSugarFactory.register_sugar(MemAccess(encoder_config))
        SyntacticSugarFactory.register_sugar(Posedge(encoder_config))
        SyntacticSugarFactory.register_sugar(Negedge(encoder_config))
        SyntacticSugarFactory.register_sugar(Change(encoder_config))
        SyntacticSugarFactory.register_sugar(NoChange(encoder_config))
        SyntacticSugarFactory.register_sugar(Ones(encoder_config))
        SyntacticSugarFactory.register_sugar(Zero(encoder_config))
        SyntacticSugarFactory.register_sugar(Dec2BV(encoder_config))

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
        SyntacticSugarFactory.init_sugar(None)
        return [x[1] for x in SyntacticSugarFactory.sugars]

class VerilogEncoder(object):
    INTERNAL = 0
    YOSYS_BTOR = 1
    YOSYS_COREIR = 2

VERILOG_INTERNAL = VerilogEncoder.INTERNAL
VERILOG_YOSYS_BTOR = VerilogEncoder.YOSYS_BTOR
VERILOG_YOSYS_COREIR = VerilogEncoder.YOSYS_COREIR

class ModelParsersFactory(object):
    parsers = []
    verilog_encoder = VerilogEncoder.YOSYS_BTOR
    # Other option -- to be deprecated soon
    # verilog_encoder = VerilogEncoder.INTERNAL

    # Additional parsers should be registered here #
    @staticmethod
    def init_parsers():
        from cosa.encoders.symbolic_transition_system import SymbolicTSParser, SymbolicSimpleTSParser
        from cosa.encoders.explicit_transition_system import ExplicitTSParser
        from cosa.encoders.btor2 import BTOR2Parser
        from cosa.encoders.coreir import CoreIRParser
        from cosa.encoders.verilog_yosys import VerilogYosysBtorParser

        ModelParsersFactory.register_parser(CoreIRParser())
        ModelParsersFactory.register_parser(SymbolicTSParser())
        ModelParsersFactory.register_parser(SymbolicSimpleTSParser())
        ModelParsersFactory.register_parser(ExplicitTSParser())
        ModelParsersFactory.register_parser(BTOR2Parser())

        if ModelParsersFactory.verilog_encoder == VerilogEncoder.INTERNAL:
            Logger.error("Internal verilog parser support is deprecated.")

        if ModelParsersFactory.verilog_encoder == VerilogEncoder.YOSYS_BTOR:
            ModelParsersFactory.register_parser(VerilogYosysBtorParser())

        if ModelParsersFactory.verilog_encoder == VerilogEncoder.YOSYS_COREIR:
            Logger.error("Not supported")

    @staticmethod
    def register_parser(parser):
        if parser.get_name() not in dict(ModelParsersFactory.parsers):
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
        from cosa.encoders.generators import ScoreBoardGenerator, FixedScoreBoardGenerator, RandomGenerator

        GeneratorsFactory.register_generator(FixedScoreBoardGenerator())
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

class ClockBehaviorsFactory(object):
    clockbehaviors = []
    default_clockbehavior = None
    default_multi_clockbehavior = None
    default_abstract_clockbehavior = None

    # Additional clockbehaviors should be registered here #
    @staticmethod
    def init_clockbehaviors():
        from cosa.encoders.clock import DeterministicClockBehavior, ConstantClockBehavior, NondeterministicClockBehavior

        ClockBehaviorsFactory.register_clockbehavior(DeterministicClockBehavior(), default=True)
        ClockBehaviorsFactory.register_clockbehavior(ConstantClockBehavior(), default_abstract=True)
        ClockBehaviorsFactory.register_clockbehavior(NondeterministicClockBehavior(), default_multi=True)

    @staticmethod
    def get_default():
        return ClockBehaviorsFactory.default_clockbehavior

    @staticmethod
    def get_default_multi():
        return ClockBehaviorsFactory.default_multi_clockbehavior

    @staticmethod
    def get_default_abstract():
        return ClockBehaviorsFactory.default_abstract_clockbehavior

    @staticmethod
    def register_clockbehavior(clockbehavior, default=False, default_abstract=False, default_multi=False):
        if clockbehavior.get_name() not in dict(ClockBehaviorsFactory.clockbehaviors):
            ClockBehaviorsFactory.clockbehaviors.append((clockbehavior.get_name(), clockbehavior))
            if default:
                ClockBehaviorsFactory.default_clockbehavior = clockbehavior
            if default_abstract:
                ClockBehaviorsFactory.default_abstract_clockbehavior = clockbehavior
            if default_multi:
                ClockBehaviorsFactory.default_multi_clockbehavior = clockbehavior


    @staticmethod
    def clockbehavior_by_name(name):
        ClockBehaviorsFactory.init_clockbehaviors()
        dprint = dict(ClockBehaviorsFactory.clockbehaviors)
        if name not in dprint:
            Logger.error("Clockbehavior \"%s\" is not registered"%name)
        return dprint[name]

    @staticmethod
    def get_clockbehaviors():
        ClockBehaviorsFactory.init_clockbehaviors()
        return [x[1] for x in ClockBehaviorsFactory.clockbehaviors]
