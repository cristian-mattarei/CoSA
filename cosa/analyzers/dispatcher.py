# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.problem import VerificationType
from cosa.encoders.formulae import StringParser
from cosa.util.logger import Logger
from cosa.encoders.coreir import CoreIRParser
from cosa.analyzers.bmc import BMC, BMCConfig
from cosa.analyzers.bmc_liveness import BMCLiveness
from cosa.problem import VerificationStatus

class ProblemSolver(object):
    def __init__(self):
        pass

    def solve_problem(self, problem, config):
        sparser = StringParser()

        bmc_config = self.problem2bmc_config(problem, config)
        bmc = BMC(problem.hts, bmc_config)
        bmc_liveness = BMCLiveness(problem.hts, bmc_config)
        res = VerificationStatus.UNK

        Logger.log("\n*** Analyzing problem %s ***"%(problem), 1)
        
        if problem.verification == VerificationType.SAFETY:
            count = 0
            list_status = []
            for (strprop, prop, types) in sparser.parse_formulae([problem.formula]):
                res, trace = bmc.safety(prop, problem.bmc_length, problem.bmc_length_min, problem.lemmas)
                problem.status = res
                problem.trace = trace

        if problem.verification == VerificationType.LIVENESS:
            count = 0
            list_status = []
            for (strprop, prop, types) in sparser.parse_formulae([problem.formula]):
                res, trace = bmc_liveness.liveness(prop, problem.bmc_length, problem.bmc_length_min)
                problem.status = res
                problem.trace = trace

        Logger.log("\n*** Result for problem %s is %s ***"%(problem, res), 1)

                    
    def solve_problems(self, problems, config):
        self.parser = CoreIRParser(problems.model_file, "rtlil", "cgralib","commonlib")
        Logger.msg("Parsing file \"%s\"... "%(problems.model_file), 0)
        hts = self.parser.parse(problems.abstract_clock)
        Logger.log("DONE", 0)
        
        for problem in problems.problems:
            problem.hts = hts
            self.solve_problem(problem, config)

    def problem2bmc_config(self, problem, config):
        bmc_config = BMCConfig()
        
        bmc_config.smt2file = problem.smt2_tracing
        bmc_config.full_trace = problem.full_trace
        bmc_config.prefix = problem.name
        bmc_config.strategy = BMCConfig.get_strategies()[0][0]
        bmc_config.skip_solving = problem.skip_solving
        bmc_config.map_function = self.parser.remap_an2or
        bmc_config.solver_name = "msat"
        bmc_config.vcd_trace = problem.vcd or config.vcd
        bmc_config.prove = problem.prove

        return bmc_config
