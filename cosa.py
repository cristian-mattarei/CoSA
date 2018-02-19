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
from util.logger import Logger

class UndefinedTypeException(Exception):
    pass


class Config(object):
    strfile = None
    verbosity = None
    
    def __init__(self):
        self.strfile = None
        self.verbosity = 1
    
def run(config):
    parser = CoreIRParser(config.strfile)
    parser.parse()

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='CoreIR Symbolic Analyzer.')

    parser.set_defaults(input_file=None)
    parser.add_argument('-i', '--input_file', metavar='input_file', type=str, required=False,
                        help='input file, CoreIR json format')

    parser.set_defaults(verbosity=1)
    parser.add_argument('-v', dest='verbosity', metavar="verbosity", type=int,
                        help="verbosity level. (Default is \"%s\")"%1)
    
    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    args = parser.parse_args()

    config = Config()
    
    config.strfile = args.input_file
    config.verbosity = args.verbosity

    Logger.verbosity = config.verbosity
    
    sys.exit(run(config))
