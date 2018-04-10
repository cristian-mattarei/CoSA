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

from cosa.analyzers.bmc import BMC, BMCConfig
from cosa.analyzers.bmc_liveness import BMCLiveness
from cosa.util.logger import Logger
from cosa.printers import PrintersFactory, PrinterType, SMVHTSPrinter
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.coreir import CoreIRParser
from cosa.encoders.formulae import StringParser
from pysmt.shortcuts import TRUE

class Config(object):
    parser = None
    strfile = None
    verbosity = 1
    simulate = False
    bmc_length = 10
    bmc_length_min = 0
    safety = None
    liveness = None
    properties = None
    lemmas = None
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
    synchronous = None
    abstract_clock = False
    skip_solving = False
    solver_name = None
    vcd = False
    prove = False
    
    def __init__(self):
        PrintersFactory.init_printers()

        self.parser = None
        self.strfile = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.bmc_length_min = 0
        self.safety = None
        self.liveness = None
        self.properties = None
        self.lemmas = None
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
        self.strategy = BMCConfig.get_strategies()[0][0]
        self.boolean = False
        self.synchronous = None
        self.abstract_clock = False
        self.skip_solving = False
        self.solver_name = "msat"
        self.vcd = False
        self.prove = False

def run(config):
    parser = CoreIRParser(config.strfile, "rtlil", "cgralib","commonlib")
    parser.boolean = config.boolean
    
    config.parser = parser
    Logger.verbosity = config.verbosity

    if config.run_passes:
        Logger.log("Running passes:", 0)
        parser.run_passes()
    
    Logger.msg("Parsing file \"%s\"... "%(config.strfile), 0)
    hts = parser.parse(config.abstract_clock)
    Logger.log("DONE", 0)

    if config.synchronous:
        with open(config.synchronous, "r") as f:
            etsparser = ExplicitTSParser()
            ats = etsparser.parse(f.read())
            hts.add_ts(ats)
    
    printsmv = True

    bmc_config = BMCConfig()

    sparser = StringParser()
    sparser.remap_or2an = parser.remap_or2an
    
    if config.assumptions is not None:
        Logger.log("Adding %d assumptions... "%len(config.assumptions), 1)
        assumps = [t[1] for t in sparser.parse_formulae(config.assumptions)]
        hts.assumptions = assumps

    lemmas = None
    if config.lemmas is not None:
        Logger.log("Adding %d lemmas... "%len(config.lemmas), 1)
        parsed_formulae = sparser.parse_formulae(config.lemmas)
        if list(set([t[2] for t in parsed_formulae]))[0][0] != False:
            Logger.error("Lemmas do not support \"next\" operators")
        lemmas = [t[1] for t in parsed_formulae]
        
        
    bmc_config.smt2file = config.smt2file

    bmc_config.full_trace = config.full_trace
    bmc_config.prefix = config.prefix
    bmc_config.strategy = config.strategy
    bmc_config.skip_solving = config.skip_solving
    bmc_config.map_function = parser.remap_an2or
    bmc_config.solver_name = config.solver_name
    bmc_config.vcd_trace = config.vcd
    bmc_config.prove = config.prove

    if config.liveness:
        bmc_liveness = BMCLiveness(hts, bmc_config)
    else:
        bmc = BMC(hts, bmc_config)

    if Logger.level(1):
        stat = []
        stat.append("Statistics (System 1):")
        stat.append("  Variables:\t%s"%(len(hts.vars)))
        stat.append("  StateVars:\t%s"%(len(hts.state_vars)))
        stat.append("  Inputs:\t%s"%(len(hts.inputs)))
        stat.append("  Outputs:\t%s"%(len(hts.outputs)))
        print("\n".join(stat))

    def trace_printed(msg, count):
        vcd_msg = ""
        if config.vcd:
            vcd_msg = " and in \"%s-id_%s.vcd\""%(config.prefix, count)
        Logger.log("%s stored in \"%s-id_%s.txt\"%s"%(msg, config.prefix, count, vcd_msg), 0)
        
    if config.translate:
        Logger.log("Writing system to \"%s\""%(config.translate), 0)
        printer = PrintersFactory.printer_by_name(config.printer)

        properties = None
        if config.properties:
            properties = sparser.parse_formulae(config.properties)
        
        with open(config.translate, "w") as f:
            f.write(printer.print_hts(hts, properties))
        
    if config.simulate:
        count = 0
        if config.properties is None:
            props = [("True", TRUE(), None)]
        else:
            props = sparser.parse_formulae(config.properties)
        for (strprop, prop, types) in props:
            Logger.log("Simulation for property \"%s\":"%(strprop), 0)
            if bmc.simulate(prop, config.bmc_length) and config.prefix:
                count += 1
                trace_printed("Execution", count)
        
    if config.safety:
        count = 0
        list_status = []
        for (strprop, prop, types) in sparser.parse_formulae(config.properties):
            Logger.log("Safety verification for property \"%s\":"%(strprop), 0)
            if not bmc.safety(prop, config.bmc_length, config.bmc_length_min, lemmas) and config.prefix:
                count += 1
                trace_printed("Counterexample", count)
                list_status.append(False)
            else:
                list_status.append(True)
                
        return list_status

    if config.liveness:
        count = 0
        list_status = []
        for (strprop, prop, types) in sparser.parse_formulae(config.properties):
            Logger.log("Liveness verification for property \"%s\":"%(strprop), 0)
            if not bmc_liveness.liveness(prop, config.bmc_length, config.bmc_length_min) and config.prefix:
                count += 1
                trace_printed("Counterexample", count)
                list_status.append(False)
            else:
                list_status.append(True)
                
        return list_status
    
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

    parser.set_defaults(liveness=False)
    parser.add_argument('--liveness', dest='liveness', action='store_true',
                       help='liveness verification using BMC.')
    
    parser.set_defaults(properties=None)
    parser.add_argument('-p', '--properties', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of invariant properties.')

    parser.set_defaults(lemmas=None)
    parser.add_argument('-l', '--lemmas', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of lemmas.')
    
    parser.set_defaults(assumptions=None)
    parser.add_argument('-a', '--assumptions', metavar='<invar assumptions list>', type=str, required=False,
                       help='comma separated list of invariant assumptions.')

    parser.set_defaults(prove=False)
    parser.add_argument('--prove', dest='prove', action='store_true',
                       help='use k-indution to prove the satisfiability of the property.')
    
    parser.set_defaults(equivalence=None)
    parser.add_argument('--equivalence', metavar='<JSON file>', type=str, required=False,
                       help='equivalence checking using BMC.')

    parser.set_defaults(fsm_check=False)
    parser.add_argument('--fsm-check', dest='fsm_check', action='store_true',
                       help='check if the state machine is deterministic.')

    parser.set_defaults(synchronous=None)
    parser.add_argument('--synchronous', metavar='<input file>', type=str, required=False,
                       help='additional state machine to add in synchronous product.')
    
    parser.set_defaults(translate=None)
    parser.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file.')

    parser.set_defaults(abstract_clock=False)
    parser.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                       help='abstracts the clock behavior.')
    
    parser.set_defaults(bmc_length=config.bmc_length)
    parser.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                        help="depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length)

    parser.set_defaults(bmc_length_min=config.bmc_length_min)
    parser.add_argument('-km', '--bmc-length-min', metavar='<BMC length>', type=int, required=False,
                        help="minimum depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length_min)
    
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

    parser.set_defaults(vcd=False)
    parser.add_argument('--vcd', dest='vcd', action='store_true',
                       help='generate traces also in vcd format.')
    
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

    parser.set_defaults(debug=False)
    parser.add_argument('--debug', dest='debug', action='store_true',
                       help='enables debug mode.')
    
    args = parser.parse_args()

    config.strfile = args.input_file
    config.simulate = args.simulate
    config.safety = args.safety
    config.liveness = args.liveness
    config.properties = args.properties
    config.lemmas = args.lemmas
    config.assumptions = args.assumptions
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.fsm_check = args.fsm_check
    config.bmc_length = args.bmc_length
    config.bmc_length_min = args.bmc_length_min
    config.full_trace = args.full_trace
    config.prefix = args.prefix
    config.run_passes = args.run_passes
    config.translate = args.translate
    config.smt2file = args.smt2
    config.strategy = args.strategy
    config.skip_solving = args.skip_solving
    config.abstract_clock = args.abstract_clock
    config.boolean = args.boolean
    config.synchronous = args.synchronous
    config.verbosity = args.verbosity
    config.vcd = args.vcd
    config.prove = args.prove

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
           (config.liveness) or \
           (config.equivalence is not None) or\
           (config.translate is not None) or\
           (config.fsm_check)):
        Logger.error("Analysis selection is necessary")
        ok = False

    if config.safety and (config.properties is None):
        Logger.error("Safety verification requires at least a property")
        ok = False

    if config.safety and (config.properties is None):
        Logger.error("Safety verification requires at least a property")
        ok = False
        
    if config.liveness and (config.properties is None):
        Logger.error("Liveness verification requires at least a property")
        ok = False

    parsing_defs = [config.properties, config.lemmas, config.assumptions]
    for i in range(len(parsing_defs)):
        if parsing_defs[i] is not None:
            if os.path.isfile(parsing_defs[i]):
                with open(parsing_defs[i]) as f:
                    parsing_defs[i] = [p.strip() for p in f.read().strip().split("\n")]
            else:
                parsing_defs[i] = [p.strip() for p in parsing_defs[i].split(",")]

    [config.properties, config.lemmas, config.assumptions] = parsing_defs                

    if not ok:
        parser.print_help()
        sys.exit(1)

    if args.debug:
        run(config)
    else:
        try:
            run(config)
        except Exception as e:
            Logger.error(str(e))
        
    
