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
    
    def __init__(self):
        self.strfile = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.safety = None
    
def run(config):
    parser = CoreIRParser(config.strfile)
    hts = parser.parse()

    bmc = BMC(hts)

    if config.simulate:
        bmc.simulate(config.bmc_length)

    if config.safety:
        bmc.safety(config.safety, config.bmc_length)
    

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='CoreIR Symbolic Analyzer.')

    parser.set_defaults(input_file=None)
    parser.add_argument('-i', '--input_file', metavar='input_file', type=str, required=False,
                        help='input file, CoreIR json format')


    parser.set_defaults(simulate=False)
    parser.add_argument('--simulate', dest='simulate', action='store_true',
                       help='simulate system using BMC')

    parser.set_defaults(safety=None)
    parser.add_argument('--safety', metavar='safety', type=str, required=False,
                       help='safety verification using BMC')

    parser.set_defaults(bmc_length=10)
    parser.add_argument('-k', '--bmc-length', metavar='bmc_length', type=int, required=False,
                        help='depth of BMC unrolling')
    
    parser.set_defaults(verbosity=1)
    parser.add_argument('-v', dest='verbosity', metavar="verbosity", type=int,
                        help="verbosity level. (Default is \"%s\")"%1)


    args = parser.parse_args()

    config = Config()
    
    config.strfile = args.input_file
    config.simulate = args.simulate
    config.safety = args.safety
    config.bmc_length = args.bmc_length
    
    config.verbosity = args.verbosity

    Logger.verbosity = config.verbosity
    
    ok = True
    
    if len(sys.argv)==1:
        ok = False

    if not(config.simulate or (config.safety is not None)):
        Logger.error("analysis selection is necessary")
        ok = False
        
    if not ok:
        parser.print_help()
        sys.exit(1)
        
    
    sys.exit(run(config))
