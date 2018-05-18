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

from cosa.problem import VerificationType
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.encoders.coreir import CoreIRParser
from cosa.analyzers.bmc import BMC, BMCConfig
from cosa.analyzers.bmc_liveness import BMCLiveness
from cosa.problem import VerificationStatus
from cosa.encoders.miter import Miter
from cosa.transition_systems import HTS
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.symbolic_transition_system import SymbolicTSParser

FLAG_SR = "["
FLAG_ST = "]"
FLAG_SP = "+"

MODEL_SP = ","

class ProblemSolver(object):
    parser = None

    def __init__(self):
        pass

    def solve_problem(self, problem, config):
        Logger.log("\n*** Analyzing problem \"%s\" ***"%(problem), 1)
        sparser = StringParser()

        bmc_config = self.problem2bmc_config(problem, config)
        bmc = BMC(problem.hts, bmc_config)
        bmc_liveness = BMCLiveness(problem.hts, bmc_config)
        res = VerificationStatus.UNK
        bmc_length = max(problem.bmc_length, config.bmc_length)
        bmc_length_min = max(problem.bmc_length_min, config.bmc_length_min)

        parsing_defs = [bmc_config.properties, bmc_config.lemmas, bmc_config.assumptions]
        for i in range(len(parsing_defs)):
            if parsing_defs[i] is not None:
                pdef_file = problem.relative_path+parsing_defs[i]
                if os.path.isfile(pdef_file):
                    with open(pdef_file) as f:
                        parsing_defs[i] = [p.strip() for p in f.read().strip().split("\n")]
                else:
                    parsing_defs[i] = [p.strip() for p in parsing_defs[i].split(MODEL_SP)]
            else:
                parsing_defs[i] = None

        [bmc_config.properties, bmc_config.lemmas, bmc_config.assumptions] = parsing_defs

        assumps = None
        lemmas = None

        if problem.verification != VerificationType.EQUIVALENCE:
            assumps = [t[1] for t in sparser.parse_formulae(bmc_config.assumptions)]
            lemmas = [t[1] for t in sparser.parse_formulae(bmc_config.lemmas)]
            for ass in assumps:
                problem.hts.add_assumption(ass)
            for lemma in lemmas:
                problem.hts.add_lemma(lemma)
            (strprop, prop, types) = sparser.parse_formulae(bmc_config.properties)[0]

        if problem.verification == VerificationType.SAFETY:
            res, trace, _ = bmc.safety(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.LIVENESS:
            res, trace = bmc_liveness.liveness(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.EVENTUALLY:
            res, trace = bmc_liveness.eventually(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.SIMULATION:
            res, trace = bmc.simulate(prop, bmc_length)
            
        if problem.verification == VerificationType.EQUIVALENCE:
            if problem.equivalence:
                problem.hts2 = self.parse_model(problem.relative_path, problem.equivalence, problem.abstract_clock, problem.symbolic_init, "System 2")

            htseq, miter_out = Miter.combine_systems(problem.hts, problem.hts2, problem.bmc_length, problem.symbolic_init, bmc_config.properties, True)

            if bmc_config.assumptions is not None:
                assumps = [t[1] for t in sparser.parse_formulae(bmc_config.assumptions)]

            if bmc_config.lemmas is not None:
                lemmas = [t[1] for t in sparser.parse_formulae(bmc_config.lemmas)]

            if assumps is not None:
                for assumption in assumps:
                    htseq.add_assumption(assumption)

            if lemmas is not None:
                for lemma in lemmas:
                    htseq.add_lemma(lemma)

            bmcseq = BMC(htseq, bmc_config)
            res, trace, t = bmcseq.safety(miter_out, problem.bmc_length, problem.bmc_length_min)
            
        problem.status = res
        problem.trace = trace

        if problem.assumptions is not None:
            problem.hts.assumptions = None

        Logger.log("\n*** Result for problem \"%s\" is %s ***"%(problem, res), 1)

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)
        
        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)
        
    def parse_model(self, relative_path, model_files, abstract_clock, symbolic_init, name=None):
        hts = HTS("System 1")

        models = model_files.split(MODEL_SP)

        for strfile in models:
            (strfile, flags) = self.get_file_flags(strfile)
            filetype = strfile.split(".")[-1]
            strfile = relative_path+strfile
            parser = None

            if filetype == CoreIRParser.get_extension():
                parser = CoreIRParser(abstract_clock, symbolic_init)
                parser.boolean = False
                self.parser = parser

            if filetype == ExplicitTSParser.get_extension():
                parser = ExplicitTSParser()

            if filetype == SymbolicTSParser.get_extension():
                parser = SymbolicTSParser()

            if parser is not None:
                if not os.path.isfile(strfile):
                    Logger.error("File \"%s\" does not exist"%strfile)

                Logger.msg("Parsing file \"%s\"... "%(strfile), 0)
                hts_a = parser.parse_file(strfile, flags)
                hts.combine(hts_a)

                Logger.log("DONE", 0)
                continue

            Logger.error("Filetype \"%s\" unsupported"%filetype)

        if Logger.level(1):
            print(hts.print_statistics(name))

        return hts

    def solve_problems(self, problems, config):
        # generate systems for each problem configuration
        systems = {}
        for si in problems.symbolic_inits:
            systems[('hts', si)] = self.parse_model(problems.relative_path, problems.model_file, problems.abstract_clock, si, "System 1")

        if problems.equivalence is not None:
            systems[('hts2', si)] = self.parse_model(problems.relative_path, problems.equivalence, problems.abstract_clock, si, "System 2")
        else:
            systems[('hts2', si)] = None

        for problem in problems.problems:
            problem.hts = systems[('hts', problem.symbolic_init)]
            problem.hts2 = systems[('hts2', problem.symbolic_init)]
            problem.abstract_clock = problems.abstract_clock
            problem.relative_path = problems.relative_path
            self.solve_problem(problem, config)

    def problem2bmc_config(self, problem, config):
        bmc_config = BMCConfig()

        config_selection = lambda problem, config: config if problem is None else problem
        
        bmc_config.smt2file = config_selection(problem.smt2_tracing, config.smt2file)
        bmc_config.full_trace = problem.full_trace or config.full_trace
        bmc_config.prefix = problem.name
        bmc_config.strategy = config_selection(problem.strategy, config.strategy)
        bmc_config.skip_solving = config_selection(problem.skip_solving, config.skip_solving)
        bmc_config.map_function = self.parser.remap_an2or
        bmc_config.solver_name = config_selection(problem.solver_name, config.solver_name)
        bmc_config.vcd_trace = problem.vcd or config.vcd
        bmc_config.prove = config_selection(problem.prove, config.prove)
        bmc_config.properties = problem.formula
        bmc_config.assumptions = problem.assumptions
        bmc_config.lemmas = problem.lemmas

        return bmc_config
