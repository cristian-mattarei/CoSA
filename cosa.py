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

from argparse import RawTextHelpFormatter

from core.coreir_parser import CoreIRParser
from analyzers.bmc import BMC
from util.logger import Logger

from core.printers import PrintersFactory, PrinterType, SMVHTSPrinter

class Config(object):
    parser = None
    strfile = None
    verbosity = 1
    simulate = False
    bmc_length = 10
    safety = None
    properties = None
    equivalence = None
    symbolic_init = None
    fsm_check = False
    full_trace = False
    prefix = None
    run_passes = False
    printer = None
    translate = None
    
    def __init__(self):
        PrintersFactory.init_printers()

        self.parser = None
        self.strfile = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.safety = None
        self.properties = None
        self.equivalence = None
        self.symbolic_init = False
        self.fsm_check = False
        self.full_trace = False
        self.prefix = None
        self.run_passes = False
        self.printer = PrintersFactory.get_default().get_name()
        self.translate = None


def parse_properties(config):
    (parser, strprops) = (config.parser, config.properties)
    props = []

    for strprop in strprops:
        try:
            props.append((strprop, parser.parse_formula(strprop)))
        except Exception as e:
            Logger.error(str(e))

    return props

    
def run(config):
    parser = CoreIRParser(config.strfile)
    config.parser = parser
    
    if config.run_passes:
        Logger.log("Running passes:", 0)
        parser.run_passes()
    
    hts = parser.parse()

    printsmv = True
    
    bmc = BMC(hts)

    bmc.config.full_trace = config.full_trace
    bmc.config.prefix = config.prefix

    if Logger.level(1):
        stat = []
        stat.append("Statistics (System 1):")
        stat.append("  Variables:\t%s"%(len(hts.vars)))
        stat.append("  StateVars:\t%s"%(len(hts.state_vars)))
        stat.append("  Inputs:\t%s"%(len(hts.inputs)))
        stat.append("  Outputs:\t%s"%(len(hts.outputs)))
        print("\n".join(stat))

    if config.translate:
        Logger.log("Writing system to \"%s\""%(config.translate), 0)
        printer = PrintersFactory.printer_by_name(config.printer)

        properties = None
        if config.properties:
            properties = parse_properties(config)
        
        with open(config.translate, "w") as f:
            f.write(printer.print_hts(hts, properties))
        
    if config.simulate:
        Logger.log("Simulation with k=%s:"%(config.bmc_length), 0)
        bmc.simulate(config.bmc_length)

    if config.safety:
        for (strprop, prop) in parse_properties(config):
            Logger.log("Safety verification for property \"%s\":"%(strprop), 0)
            bmc.safety(prop, config.bmc_length)

    if config.equivalence:
        Logger.log("Equivalenche check with k=%s:"%(config.bmc_length), 0)
        parser2 = CoreIRParser(config.equivalence)
        
        if config.run_passes:
            Logger.log("Running passes:", 0)
            parser2.run_passes()
        
        hts2 = parser2.parse()

        if Logger.level(1):
            stat = []
            stat.append("Statistics (System 2):")
            stat.append("  Variables:\t%s"%(len(hts2.vars)))
            stat.append("  StateVars:\t%s"%(len(hts2.state_vars)))
            stat.append("  Inputs:\t%s"%(len(hts2.inputs)))
            stat.append("  Outputs:\t%s"%(len(hts2.outputs)))
            print("\n".join(stat))
        
        bmc.equivalence(hts2, config.bmc_length, config.symbolic_init)

    if config.fsm_check:
        Logger.log("Checking FSM:", 0)

        bmc.fsm_check()
        

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='CoreIR Symbolic Analyzer.', formatter_class=RawTextHelpFormatter)

    config = Config()
    printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]
    
    parser.set_defaults(input_file=None)
    parser.add_argument('-i', '--input_file', metavar='<JSON file>', type=str, required=False,
                        help='input file, CoreIR json format')
    
    parser.set_defaults(simulate=False)
    parser.add_argument('--simulate', dest='simulate', action='store_true',
                       help='simulate system using BMC')

    parser.set_defaults(safety=False)
    parser.add_argument('--safety', dest='safety', action='store_true',
                       help='safety verification using BMC')
    
    parser.set_defaults(properties=None)
    parser.add_argument('-p', '--properties', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of invariant properties')
    
    parser.set_defaults(equivalence=None)
    parser.add_argument('--equivalence', metavar='<JSON file>', type=str, required=False,
                       help='equivalence checking using BMC')

    parser.set_defaults(fsm_check=False)
    parser.add_argument('--fsm-check', dest='fsm_check', action='store_true',
                       help='check if the state machine is deterministic')

    parser.set_defaults(translate=None)
    parser.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file')

    parser.set_defaults(bmc_length=config.bmc_length)
    parser.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                        help="depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length)
    
    parser.set_defaults(symbolic_init=config.symbolic_init)
    parser.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                       help='symbolic inititial state for equivalence checking. (Default is \"%s\")'%config.symbolic_init)

    parser.set_defaults(run_passes=config.run_passes)
    parser.add_argument('--run-passes', dest='run_passes', action='store_true',
                        help='run necessary passes to process the CoreIR file. (Default is \"%s\")'%config.run_passes)
    
    parser.set_defaults(full_trace=config.full_trace)
    parser.add_argument('--full-trace', dest='full_trace', action='store_true',
                       help="show all variables in the counterexamples. (Default is \"%s\")"%config.full_trace)

    parser.set_defaults(prefix=None)
    parser.add_argument('--prefix', metavar='<prefix location>', type=str, required=False,
                       help='write the counterexamples with specified location prefix')

    parser.set_defaults(printer=config.printer)
    parser.add_argument('--printer', metavar='printer', type=str, nargs='?', 
                        help='select the printer between (Default is \"%s\"):\n%s'%(config.printer, "\n".join(printers)))
    
    parser.set_defaults(verbosity=config.verbosity)
    parser.add_argument('-v', dest='verbosity', metavar="<integer level>", type=int,
                        help="verbosity level. (Default is \"%s\")"%config.verbosity)


    args = parser.parse_args()

    
    config.strfile = args.input_file
    config.simulate = args.simulate
    config.safety = args.safety
    config.properties = args.properties
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.fsm_check = args.fsm_check
    config.bmc_length = args.bmc_length
    config.full_trace = args.full_trace
    config.prefix = args.prefix
    config.run_passes = args.run_passes
    config.translate = args.translate
    
    config.verbosity = args.verbosity

    Logger.verbosity = config.verbosity
    
    ok = True
    
    if len(sys.argv)==1:
        ok = False

    if args.printer in [str(x.get_name()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]:
        config.printer = args.printer
    else:
        Logger.error("Printer \"%s\" not found"%(args.printer))
        
    if not(config.simulate or \
           (config.safety) or \
           (config.equivalence is not None) or\
           (config.translate is not None) or\
           (config.fsm_check)):
        Logger.error("Analysis selection is necessary")
        ok = False

    if config.safety and (config.properties is None):
        Logger.error("Safety verification requires at least a property")
        ok = False

    if config.properties is not None:
        config.properties = [p.strip() for p in config.properties.split(",")]
        
    if not ok:
        parser.print_help()
        sys.exit(1)
        
    
    sys.exit(run(config))
