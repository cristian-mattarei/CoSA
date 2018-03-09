#!/usr/bin/env python

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
import os

from argparse import RawTextHelpFormatter

from cosa.core.coreir_parser import CoreIRParser
from cosa.analyzers.bmc import BMC, BMCConfig
from cosa.util.logger import Logger
from cosa.printers import PrintersFactory, PrinterType, SMVHTSPrinter

class Config(object):
    parser = None
    strfile = None
    verbosity = 1
    simulate = False
    bmc_length = 10
    safety = None
    properties = None
    assumptions = None
    equivalence = None
    symbolic_init = None
    fsm_check = False
    full_trace = False
    prefix = None
    run_passes = False
    printer = None
    translate = None
    smt2file = None
    strategy = None
    boolean = None
    
    def __init__(self):
        PrintersFactory.init_printers()

        self.parser = None
        self.strfile = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.safety = None
        self.properties = None
        self.assumptions = None
        self.equivalence = None
        self.symbolic_init = False
        self.fsm_check = False
        self.full_trace = False
        self.prefix = None
        self.run_passes = False
        self.printer = PrintersFactory.get_default().get_name()
        self.translate = None
        self.smt2file = None
        self.strategy = None
        self.boolean = False

def parse_formulae(config, strforms):
    parser = config.parser
    formulae = []

    for strform in strforms:
        try:
            formulae.append((strform, parser.parse_formula(strform)))
        except Exception as e:
            Logger.error(str(e))

    return formulae

    
def run(config):
    parser = CoreIRParser(config.strfile, "rtlil", "cgralib","commonlib")
    parser.boolean = config.boolean
    
    config.parser = parser
    
    if config.run_passes:
        Logger.log("Running passes:", 0)
        parser.run_passes()
    
    Logger.msg("Parsing file \"%s\"... "%(config.strfile), 0)
    hts = parser.parse(config.abstract_clock)
    Logger.log("DONE", 0)

    printsmv = True

    bmc_config = BMCConfig()

    if config.assumptions is not None:
        Logger.log("Adding %d assumptions... "%len(config.assumptions), 1)
        parsed_assumps = parse_formulae(config, config.assumptions)
        assumps = [t[1] for t in parse_formulae(config, config.assumptions)]
        hts.assumptions = assumps

    bmc_config.smt2file = config.smt2file

    bmc_config.full_trace = config.full_trace
    bmc_config.prefix = config.prefix
    bmc_config.strategy = config.strategy
    bmc_config.skip_solving = config.skip_solving

    bmc = BMC(hts, bmc_config)
    
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
            properties = parse_formulae(config, config.properties)
        
        with open(config.translate, "w") as f:
            f.write(printer.print_hts(hts, properties))
        
    if config.simulate:
        Logger.log("Simulation with k=%s:"%(config.bmc_length), 0)
        bmc.simulate(config.bmc_length)

    if config.safety:
        for (strprop, prop) in parse_formulae(config, config.properties):
            Logger.log("Safety verification for property \"%s\":"%(strprop), 0)
            bmc.safety(prop, config.bmc_length)

    if config.equivalence:
        parser2 = CoreIRParser(config.equivalence)
        
        if config.run_passes:
            Logger.log("Running passes:", 0)
            parser2.run_passes()
        
        Logger.msg("Parsing file \"%s\"... "%(config.equivalence), 0)
        hts2 = parser2.parse(config.abstract_clock)
        Logger.log("DONE", 0)

        symb = " (symbolic init)" if config.symbolic_init else ""
        Logger.log("Equivalence checking%s with k=%s:"%(symb, config.bmc_length), 0)

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
    
    parser.set_defaults(input_file=None)
    parser.add_argument('-i', '--input_file', metavar='<JSON file>', type=str, required=True,
                        help='input file, CoreIR json format.')
    
    parser.set_defaults(simulate=False)
    parser.add_argument('--simulate', dest='simulate', action='store_true',
                       help='simulate system using BMC.')

    parser.set_defaults(safety=False)
    parser.add_argument('--safety', dest='safety', action='store_true',
                       help='safety verification using BMC.')
    
    parser.set_defaults(properties=None)
    parser.add_argument('-p', '--properties', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of invariant properties.')

    parser.set_defaults(assumptions=None)
    parser.add_argument('-a', '--assumptions', metavar='<invar assumptions list>', type=str, required=False,
                       help='comma separated list of invariant assumptions.')
    
    parser.set_defaults(equivalence=None)
    parser.add_argument('--equivalence', metavar='<JSON file>', type=str, required=False,
                       help='equivalence checking using BMC.')

    parser.set_defaults(fsm_check=False)
    parser.add_argument('--fsm-check', dest='fsm_check', action='store_true',
                       help='check if the state machine is deterministic.')

    parser.set_defaults(translate=None)
    parser.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file.')

    parser.set_defaults(abstract_clock=False)
    parser.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                       help='abstracts the clock behavior.')
    
    parser.set_defaults(bmc_length=config.bmc_length)
    parser.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                        help="depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length)
    
    parser.set_defaults(symbolic_init=config.symbolic_init)
    parser.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                       help='symbolic inititial state for equivalence checking. (Default is \"%s\")'%config.symbolic_init)

    parser.set_defaults(boolean=config.boolean)
    parser.add_argument('--boolean', dest='boolean', action='store_true',
                        help='interprets single bits as Booleans instead of 1-bit Bitvector. (Default is \"%s\")'%config.boolean)
    
    parser.set_defaults(run_passes=config.run_passes)
    parser.add_argument('--run-passes', dest='run_passes', action='store_true',
                        help='run necessary passes to process the CoreIR file. (Default is \"%s\")'%config.run_passes)
    
    parser.set_defaults(full_trace=config.full_trace)
    parser.add_argument('--full-trace', dest='full_trace', action='store_true',
                       help="show all variables in the counterexamples. (Default is \"%s\")"%config.full_trace)

    parser.set_defaults(prefix=None)
    parser.add_argument('--prefix', metavar='<prefix location>', type=str, required=False,
                       help='write the counterexamples with specified location prefix.')

    printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]
    
    parser.set_defaults(printer=config.printer)
    parser.add_argument('--printer', metavar='printer', type=str, nargs='?', 
                        help='select the printer between (Default is \"%s\"):\n%s'%(config.printer, "\n".join(printers)))

    strategies = [" - \"%s\": %s"%(x[0], x[1]) for x in BMCConfig.get_strategies()]
    defstrategy = BMCConfig.get_strategies()[0][0]
    parser.set_defaults(strategy=defstrategy)
    parser.add_argument('--strategy', metavar='strategy', type=str, nargs='?', 
                        help='select the BMC strategy between (Default is \"%s\"):\n%s'%(defstrategy, "\n".join(strategies)))
    
    parser.set_defaults(smt2=None)
    parser.add_argument('--smt2', metavar='<smt-lib2 file>', type=str, required=False,
                       help='generates the smtlib2 encoding for a BMC call.')

    parser.set_defaults(skip_solving=False)
    parser.add_argument('--skip-solving', dest='skip_solving', action='store_true',
                       help='does not call the solver (used with --smt2 parameter).')
    
    parser.set_defaults(verbosity=config.verbosity)
    parser.add_argument('-v', dest='verbosity', metavar="<integer level>", type=int,
                        help="verbosity level. (Default is \"%s\")"%config.verbosity)

    args = parser.parse_args()

    config.strfile = args.input_file
    config.simulate = args.simulate
    config.safety = args.safety
    config.properties = args.properties
    config.assumptions = args.assumptions
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.fsm_check = args.fsm_check
    config.bmc_length = args.bmc_length
    config.full_trace = args.full_trace
    config.prefix = args.prefix
    config.run_passes = args.run_passes
    config.translate = args.translate
    config.smt2file = args.smt2
    config.strategy = args.strategy
    config.skip_solving = args.skip_solving
    config.abstract_clock = args.abstract_clock
    config.boolean = args.boolean
    
    config.verbosity = args.verbosity

    Logger.verbosity = config.verbosity
    
    ok = True
    
    if len(sys.argv)==1:
        ok = False
        
    if args.printer in [str(x.get_name()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]:
        config.printer = args.printer
    else:
        Logger.error("Printer \"%s\" not found"%(args.printer))
        ok = False

    if args.strategy not in [s[0] for s in BMCConfig.get_strategies()]:
        Logger.error("Strategy \"%s\" not found"%(args.strategy))
        ok = False
        
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
        if os.path.isfile(config.properties):
            with open(config.properties) as f:
                config.properties = [p.strip() for p in f.read().strip().split("\n")]
        else:
            config.properties = [p.strip() for p in config.properties.split(",")]

    if config.assumptions is not None:
        if os.path.isfile(config.assumptions):
            with open(config.assumptions) as f:
                config.assumptions = [a.strip() for a in f.read().strip().split("\n")]
        else:
            config.assumptions = [a.strip() for a in config.assumptions.split(",")]

    if not ok:
        parser.print_help()
        sys.exit(1)
        
    
    sys.exit(run(config))
