# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import configparser
import copy

from cosa.util.logger import Logger
from cosa.util.utils import auto_convert
from cosa.encoders.formulae import StringParser

DEFAULT = "DEFAULT"
VERIFICATION = "verification"
LIVENESS = "liveness"
SAFETY = "safety"
FORMULA = "formula"
MODEL_FILE = "model_file"

class VerificationStatus(object):
    UNK = 0
    TRUE = 1
    FALSE = -1

class VerificationType(object):
    SAFETY = 0
    LIVENESS = 1

class Problems(object):
    problems = None
    model_file = None
    bmc_length = 10

    def __init__(self):
        self.problems = []

    def add_problem(self, problem):
        self.problems.append(problem)

    def generate_problem(self, name, pbm_values):
        pbm = Problem()
        
        if VERIFICATION not in pbm_values:
            Logger.error("Verification type missing in problem \"%s\""%(name))
        else:
            pbm.set_verification(pbm_values[VERIFICATION].lower())
            del(pbm_values[VERIFICATION])

        for attr,value in pbm_values.items():
            if hasattr(pbm, attr):
                setattr(pbm, attr, auto_convert(value))
            else:
                Logger.error("Attribute \"%s\" not found"%attr)

        return pbm
        
    def load_problems(self, problems_file):
        config = configparser.ConfigParser()
        config.optionxform=str
        with open(problems_file, "r") as f:
            config.read_string(u""+f.read())

        default_values = None

        for value in config:
            problem = config[value]
            if DEFAULT == value:
                default_values = dict(problem)

                for attr,value in default_values.items():
                    if hasattr(self, attr):
                        setattr(self, attr, auto_convert(value))
                    else:
                        Logger.error("Attribute \"%s\" not found"%attr)
                continue
            pbm = copy.copy(default_values)
            pbm.update(dict(problem))
            pbm = self.generate_problem(value, pbm)
            pbm.name = value
            self.add_problem(pbm)

class Problem(object):
    assumptions = None
    lemmas = None
    strategy = None
    symbolic_init = None
    smt2_tracing = None

    trace_all_vars = None
    trace_diff_vars = None
    trace_prefix = None

    verbosity = None
    description = None

    status = VerificationStatus.UNK
    verification = None
    formula = None
    prove = False
    bmc_length = 10
    bmc_length_min = 0
    full_trace = True
    
    model_file = None
    name = None
    
    def __init__(self):
        self.status = VerificationStatus.UNK
        self.description = ""

    def __repr__(self):
        return "%s, %s"%(self.model_file, self.description, )

    def set_verification(self, value):
        if value == LIVENESS:
            self.verification = VerificationType.LIVENESS
            return

        if value == SAFETY:
            self.verification = VerificationType.SAFETY
            return

        Logger.error("Unknown verification type \"%s\""%value)
