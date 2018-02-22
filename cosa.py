# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import sys
import coreir
import argparse

from core.coreir_parser import CoreIRParser
from analyzers.bmc import BMC
from util.logger import Logger

class Config(object):
    strfile = None
    verbosity = 1
    simulate = False
    bmc_length = 10
    safety = None
    equivalence = None
    symbolic_init = None
    fsm_check = False
    full_trace = False
    trace_file = None
    
    def __init__(self):
        self.strfile = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.safety = None
        self.equivalence = None
        self.symbolic_init = False
        self.fsm_check = False
        self.full_trace = False
        self.trace_file = None
    
def run(config):
    parser = CoreIRParser(config.strfile)
    hts = parser.parse()

    bmc = BMC(hts)

    bmc.config.full_trace = config.full_trace
    bmc.config.trace_file = config.trace_file

    if config.simulate:
        bmc.simulate(config.bmc_length)

    if config.safety:
        bmc.safety(config.safety, config.bmc_length)

    if config.equivalence:
        parser2 = CoreIRParser(config.equivalence)
        hts2 = parser2.parse()
        bmc.equivalence(hts2, config.bmc_length, config.symbolic_init)

    if config.fsm_check:
        bmc.equivalence(hts, 1, True, False)
        

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='CoreIR Symbolic Analyzer.')

    parser.set_defaults(input_file=None)
    parser.add_argument('-i', '--input_file', metavar='<JSON file>', type=str, required=False,
                        help='input file, CoreIR json format')


    parser.set_defaults(simulate=False)
    parser.add_argument('--simulate', dest='simulate', action='store_true',
                       help='simulate system using BMC')

    parser.set_defaults(safety=None)
    parser.add_argument('--safety', metavar='<property>', type=str, required=False,
                       help='safety verification using BMC')

    parser.set_defaults(equivalence=None)
    parser.add_argument('--equivalence', metavar='<JSON file>', type=str, required=False,
                       help='equivalence checking using BMC')

    parser.set_defaults(symbolic_init=False)
    parser.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                       help='symbolic inititial state for equivalence checking')

    parser.set_defaults(fsm_check=False)
    parser.add_argument('--fsm-check', dest='fsm_check', action='store_true',
                       help='check if the state machine is deterministic')

    parser.set_defaults(full_trace=False)
    parser.add_argument('--full-trace', dest='full_trace', action='store_true',
                       help='show all variables in the counterexamples')

    parser.set_defaults(trace=None)
    parser.add_argument('--trace', metavar='<trace file>', type=str, required=False,
                       help='write the counterexample to file')
    
    parser.set_defaults(bmc_length=10)
    parser.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                        help='depth of BMC unrolling')
    
    parser.set_defaults(verbosity=1)
    parser.add_argument('-v', dest='verbosity', metavar="<integer level>", type=int,
                        help="verbosity level. (Default is \"%s\")"%1)


    args = parser.parse_args()

    config = Config()
    
    config.strfile = args.input_file
    config.simulate = args.simulate
    config.safety = args.safety
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.fsm_check = args.fsm_check
    config.bmc_length = args.bmc_length
    config.full_trace = args.full_trace
    config.trace_file = args.trace
    
    config.verbosity = args.verbosity

    Logger.verbosity = config.verbosity
    
    ok = True
    
    if len(sys.argv)==1:
        ok = False

    if not(config.simulate or \
           (config.safety is not None) or \
           (config.equivalence is not None) or\
           (config.fsm_check)):
        Logger.error("analysis selection is necessary")
        ok = False
        
    if not ok:
        parser.print_help()
        sys.exit(1)
        
    
    sys.exit(run(config))
