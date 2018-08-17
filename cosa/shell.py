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
import argparse
import os
import pickle

from argparse import RawTextHelpFormatter

from cosa.analyzers.dispatcher import ProblemSolver
from cosa.analyzers.mcsolver import MCConfig
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.utils.logger import Logger
from cosa.printers import PrintersFactory, PrinterType, SMVHTSPrinter
from cosa.encoders.monitors import MonitorsFactory
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.symbolic_transition_system import SymbolicTSParser
from cosa.encoders.coreir import CoreIRParser
from cosa.encoders.formulae import StringParser
from cosa.encoders.miter import Miter
from cosa.encoders.ltl import ltl_reset_env, LTLParser
from cosa.problem import Problems, VerificationStatus, VerificationType
from cosa.representation import HTS

from pysmt.shortcuts import TRUE, reset_env, get_env


class Config(object):
    parser = None
    strfiles = None
    verbosity = 1
    simulate = False
    bmc_length = 10
    bmc_length_min = 0
    safety = None
    ltl = None
    properties = None
    lemmas = None
    assumptions = None
    equivalence = None
    symbolic_init = None
    fsm_check = False
    full_trace = False
    trace_vars_change = False
    trace_all_vars = False
    prefix = None
    run_passes = False
    printer = None
    translate = None
    smt2file = None
    strategy = None
    boolean = None
    abstract_clock = False
    no_clock = False
    skip_solving = False
    pickle_file = None
    solver_name = None
    vcd = False
    prove = False
    incremental = True
    deterministic = False
    time = False
    monitors = None
    force_expected = False

    def __init__(self):
        PrintersFactory.init_printers()

        self.parser = None
        self.strfiles = None
        self.verbosity = 1
        self.simulate = False
        self.bmc_length = 10
        self.bmc_length_min = 0
        self.safety = None
        self.ltl = None
        self.properties = None
        self.lemmas = None
        self.assumptions = None
        self.equivalence = None
        self.symbolic_init = False
        self.fsm_check = False
        self.full_trace = False
        self.trace_vars_change = False
        self.trace_all_vars = False
        self.prefix = None
        self.run_passes = False
        self.printer = PrintersFactory.get_default().get_name()
        self.translate = None
        self.smt2file = None
        self.strategy = MCConfig.get_strategies()[0][0]
        self.boolean = False
        self.abstract_clock = False
        self.no_clock = False        
        self.skip_solving = False
        self.pickle_file = None
        self.solver_name = "msat"
        self.vcd = False
        self.prove = False
        self.incremental = True
        self.deterministic = False
        self.time = False
        
def trace_printed(msg, hr_trace, vcd_trace):
    vcd_msg = ""
    if vcd_trace:
        vcd_msg = " and in \"%s\""%(vcd_trace)
    Logger.log("%s stored in \"%s\"%s"%(msg, hr_trace, vcd_msg), 0)

def print_trace(msg, trace, index, prefix):
    trace_hr, trace_vcd = trace

    hr_trace_file = None
    vcd_trace_file = None

    if prefix:
        if trace_hr:
            hr_trace_file = "%s-%s.txt"%(prefix, index)
            with open(hr_trace_file, "w") as f:
                f.write(trace_hr)

        if trace_vcd:
            vcd_trace_file = "%s-%s.vcd"%(prefix, index)
            with open(vcd_trace_file, "w") as f:
                f.write(trace_vcd)

        trace_printed(msg, hr_trace_file, vcd_trace_file)

    else:
        Logger.log("%s:"%msg, 0)
        Logger.log(trace_hr, 0)

def get_file_flags(strfile):
    if "[" not in strfile:
        return (strfile, [])
    
    (strfile, flags) = (strfile[:strfile.index("[")], strfile[strfile.index("[")+1:strfile.index("]")].split(","))
    return (strfile, flags)
                        
def run_verification(config):
    reset_env()
    Logger.verbosity = config.verbosity

    coreir_parser = None
    ets_parser = None
    sts_parser = None

    if config.ltl:
        ltl_reset_env()
    
    hts = HTS("Top level")

    if config.strfiles[0][-4:] != ".pkl":
        ps = ProblemSolver()
        (hts, invar_props, ltl_props) = ps.parse_model("./", config.strfiles, config.abstract_clock, config.symbolic_init, deterministic=config.deterministic, boolean=config.boolean, no_clock=config.no_clock)
        config.parser = ps.parser

        if config.pickle_file:
            Logger.msg("Pickling model to %s\n"%(config.pickle_file), 1)
            sys.setrecursionlimit(50000)
            with open(config.pickle_file, "wb") as f:
                pickle.dump(hts, f)
    else:
        if config.pickle_file:
            raise RuntimeError("Don't need to re-pickle the input file %s"%(config.strfile))

        Logger.msg("Loading pickle file %s\n"%(config.strfile), 0)
        with open(config.pickle_file, "rb") as f:
            hts = pickle.load(f)
        Logger.log("DONE", 0)

    printsmv = True

    mc_config = MCConfig()

    sparser = StringParser()
    sparser.remap_or2an = config.parser.remap_or2an
    ltlparser = LTLParser()

    # if equivalence checking wait to add assumptions to combined system
    if config.assumptions is not None and config.equivalence is None:
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
        hts.lemmas = lemmas

    mc_config.smt2file = config.smt2file

    mc_config.full_trace = config.full_trace
    mc_config.trace_vars_change = config.trace_vars_change
    mc_config.trace_all_vars = config.trace_all_vars
    mc_config.prefix = config.prefix
    mc_config.strategy = config.strategy
    mc_config.skip_solving = config.skip_solving
    mc_config.map_function = config.parser.remap_an2or
    mc_config.solver_name = config.solver_name
    mc_config.vcd_trace = config.vcd
    mc_config.prove = config.prove
    mc_config.incremental = config.incremental

    if config.ltl:
        bmc_ltl = BMCLTL(hts, mc_config)
    else:
        bmc_safety = BMCSafety(hts, mc_config)

    if config.translate:
        Logger.log("Writing system to \"%s\""%(config.translate), 0)
        printer = PrintersFactory.printer_by_name(config.printer)

        props = []
        if config.ltl:
            props += ltlparser.parse_formulae(config.properties)
            props += [(str(p), p, None) for p in ltl_props]
        else:
            props += sparser.parse_formulae(config.properties)
            props += [(str(p), p, None) for p in invar_props]

        with open(config.translate, "w") as f:
            f.write(printer.print_hts(hts, props))

    if config.simulate:
        count = 0
        if config.properties is None:
            props = [("True", TRUE(), None)]
        else:
            props = sparser.parse_formulae(config.properties)
        for (strprop, prop, _) in props:
            Logger.log("Simulation for property \"%s\":"%(strprop), 0)
            res, trace = bmc_safety.simulate(prop, config.bmc_length)
            if res == VerificationStatus.TRUE:
                count += 1
                print_trace("Execution", trace, count, config.prefix)
            else:
                Logger.log("No execution found", 0)

    if config.safety:
        count = 0
        props = sparser.parse_formulae(config.properties)
        props += [(str(p), p, None) for p in invar_props]
        if len(props) == 0:
            Logger.warning("Safety verification requires at least a property")
            
        for (strprop, prop, _) in props:
            Logger.log("Safety verification for property \"%s\":"%(strprop), 0)
            res, trace, t = bmc_safety.safety(prop, config.bmc_length, config.bmc_length_min)
            Logger.log("\nProperty is %s"%res, 0)
            if res == VerificationStatus.FALSE:
                count += 1
                print_trace("Counterexample", trace, count, config.prefix)

        return 0
    
    if config.equivalence or config.fsm_check:

        if config.equivalence:
            parser2 = CoreIRParser(config.abstract_clock, config.symbolic_init)

            if config.run_passes:
                Logger.log("Running passes:", 0)
                parser2.run_passes()

            Logger.msg("Parsing file \"%s\"... "%(config.equivalence), 0)
            hts2 = parser2.parse_file(config.equivalence)
            Logger.log("DONE", 0)

            symb = " (symbolic init)" if config.symbolic_init else ""
            Logger.log("Equivalence checking%s with k=%s:"%(symb, config.bmc_length), 0)

            if Logger.level(1):
                print(hts2.print_statistics("System 2", Logger.level(2)))
        else:
            hts2 = hts
                
        # TODO: Make incremental solving optional
        htseq, miter_out = Miter.combine_systems(hts, hts2, config.bmc_length, config.symbolic_init, config.properties, True)

        if config.assumptions is not None:
            Logger.log("Adding %d assumptions to combined system... "%len(config.assumptions), 1)
            assumps = [t[1] for t in sparser.parse_formulae(config.assumptions)]
            htseq.assumptions = assumps

        # create bmc object for combined system
        bmcseq = BMC(htseq, mc_config)
        res, trace, t = bmcseq.safety(miter_out, config.bmc_length, config.bmc_length_min)

        msg = "Systems are %s equivalent" if config.equivalence else "System is%s deterministic"
        
        if res == VerificationStatus.FALSE:
            Logger.log(msg%(" not"), 0)
            print_trace("Counterexample", trace, 1, config.prefix)
        elif res == VerificationStatus.UNK:
            if config.symbolic_init:
                # strong equivalence with symbolic initial state
                Logger.log(msg%(""), 0)
            else:
                Logger.log(msg%("")+" up to k=%i"%t, 0)
        else:
            Logger.log(msg%("")+" up to k=%i"%t, 0)

    if config.ltl:
        count = 0
        props = ltlparser.parse_formulae(config.properties)
        props += [(str(p), p, None) for p in ltl_props]
        if len(props) == 0:
            Logger.warning("LTL verification requires at least a property")
            
        for (strprop, prop, _) in props:
            Logger.log("LTL verification for property \"%s\":"%(strprop), 0)
            res, trace, t = bmc_ltl.ltl(prop, config.bmc_length, config.bmc_length_min)
            Logger.log("\nProperty is %s"%res, 0)
            if res == VerificationStatus.FALSE:
                count += 1
                print_trace("Counterexample", trace, count, config.prefix)

        return 0
            
def run_problems(problems, config):
    reset_env()
    Logger.verbosity = config.verbosity
    pbms = Problems()
    psol = ProblemSolver()
    pbms.load_problems(problems)
    psol.solve_problems(pbms, config)

    global_status = 0
    
    Logger.log("\n*** SUMMARY ***", 0)

    for pbm in pbms.problems:
        unk_k = "" if pbm.status != VerificationStatus.UNK else "\nBMC depth: %s"%pbm.bmc_length
        Logger.log("\n** Problem %s **"%(pbm.name), 0)
        Logger.log("Description: %s"%(pbm.description), 0)
        Logger.log("Result: %s%s"%(pbm.status, unk_k), 0)
        if (pbm.expected is not None):
            expected = VerificationStatus.convert(pbm.expected) == pbm.status
            Logger.log("Expected: %s"%("OK" if expected else "WRONG"), 0)
            if not expected:
                global_status = 1

        assert not(config.force_expected and (pbm.expected is None))

        prefix = config.prefix if config.prefix is not None else pbm.trace_prefix
        
        if (pbm.verification != VerificationType.SIMULATION) and (pbm.status == VerificationStatus.FALSE):
            print_trace("Counterexample", pbm.trace, pbm.name, prefix)

        if (pbm.verification == VerificationType.SIMULATION) and (pbm.status == VerificationStatus.TRUE):
            print_trace("Execution", pbm.trace, pbm.name, prefix)

        if pbm.time:
            Logger.log("Time: %.2f sec"%(pbm.time), 0)
            
    return global_status
            
def main():
    parser = argparse.ArgumentParser(description='CoreIR Symbolic Analyzer.', formatter_class=RawTextHelpFormatter)

    config = Config()

    # Main inputs

    in_options = parser.add_argument_group('input options')
    
    in_options.set_defaults(input_files=None)
    in_options.add_argument('-i', '--input_files', metavar='<input files>', type=str, required=False,
                        help='comma separated list of input files.')

    in_options.set_defaults(problems=None)
    in_options.add_argument('--problems', metavar='<problems file>', type=str, required=False,
                       help='problems file describing the verifications to be performed.')

    # Verification Options

    ver_options = parser.add_argument_group('analysis')
    
    ver_options.set_defaults(safety=False)
    ver_options.add_argument('--safety', dest='safety', action='store_true',
                       help='safety verification using BMC.')

    ver_options.set_defaults(ltl=False)
    ver_options.add_argument('--ltl', dest='ltl', action='store_true',
                       help='ltl verification using BMC.')
    
    ver_options.set_defaults(simulate=False)
    ver_options.add_argument('--simulate', dest='simulate', action='store_true',
                       help='simulate system using BMC.')

    ver_options.set_defaults(equivalence=None)
    ver_options.add_argument('--equivalence', metavar='<input files>', type=str, required=False,
                       help='equivalence checking using BMC.')

    ver_options.set_defaults(fsm_check=False)
    ver_options.add_argument('--fsm-check', dest='fsm_check', action='store_true',
                       help='check if the state machine is deterministic.')
    
    # Verification parameters

    ver_params = parser.add_argument_group('verification parameters')
    
    ver_params.set_defaults(properties=None)
    ver_params.add_argument('-p', '--properties', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of properties.')

    ver_params.set_defaults(bmc_length=config.bmc_length)
    ver_params.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                        help="depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length)

    ver_params.set_defaults(bmc_length_min=config.bmc_length_min)
    ver_params.add_argument('-km', '--bmc-length-min', metavar='<BMC length>', type=int, required=False,
                        help="minimum depth of BMC unrolling. (Default is \"%s\")"%config.bmc_length_min)
    
    ver_params.set_defaults(lemmas=None)
    ver_params.add_argument('-l', '--lemmas', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of lemmas.')

    ver_params.set_defaults(assumptions=None)
    ver_params.add_argument('-a', '--assumptions', metavar='<invar assumptions list>', type=str, required=False,
                       help='comma separated list of invariant assumptions.')

    # monitors = [" - \"%s\": %s, with parameters (%s)"%(x.get_name(), x.get_desc(), x.get_interface()) for x in MonitorsFactory.get_monitors()]

    # ver_params.add_argument('--monitors', metavar='monitors', type=str, nargs='?',
    #                     help='comma separated list of monitors instantiation. Possible types:\n%s'%("\n".join(monitors)))
    
    ver_params.set_defaults(prove=False)
    ver_params.add_argument('--prove', dest='prove', action='store_true',
                       help='use indution to prove the satisfiability of the property.')

    strategies = [" - \"%s\": %s"%(x[0], x[1]) for x in MCConfig.get_strategies()]
    defstrategy = MCConfig.get_strategies()[0][0]
    ver_params.set_defaults(strategy=defstrategy)
    ver_params.add_argument('--strategy', metavar='strategy', type=str, nargs='?',
                        help='select the BMC strategy between (Default is \"%s\"):\n%s'%(defstrategy, "\n".join(strategies)))

    ver_params.set_defaults(ninc=False)
    ver_params.add_argument('--ninc', dest='ninc', action='store_true',
                       help='disables incrementality.')
    
    ver_params.set_defaults(solver_name=config.solver_name)
    ver_params.add_argument('--solver-name', metavar='<Solver Name>', type=str, required=False,
                        help="name of SMT solver to be use. (Default is \"%s\")"%config.solver_name)
    
    # Encoding parameters

    enc_params = parser.add_argument_group('encoding')

    enc_params.set_defaults(no_clock=False)
    enc_params.add_argument('--no-clock', dest='no_clock', action='store_true',
                       help='does not add the clock behavior.')
    
    enc_params.set_defaults(abstract_clock=False)
    enc_params.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                       help='abstracts the clock behavior.')

    enc_params.set_defaults(symbolic_init=config.symbolic_init)
    enc_params.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                       help='symbolic inititial state for equivalence checking. (Default is \"%s\")'%config.symbolic_init)

    enc_params.set_defaults(boolean=config.boolean)
    enc_params.add_argument('--boolean', dest='boolean', action='store_true',
                        help='interprets single bits as Booleans instead of 1-bit Bitvector. (Default is \"%s\")'%config.boolean)

    # enc_params.set_defaults(run_passes=config.run_passes)
    # enc_params.add_argument('--run-passes', dest='run_passes', action='store_true',
    #                     help='run necessary passes to process the CoreIR file. (Default is \"%s\")'%config.run_passes)
    
    # Printing parameters

    print_params = parser.add_argument_group('trace printing')

    print_params.set_defaults(trace_vars_change=config.trace_vars_change)
    print_params.add_argument('--trace-vars-change', dest='trace_vars_change', action='store_true',
                       help="show variable assignments in the counterexamples even when unchanged. (Default is \"%s\")"%config.trace_vars_change)

    print_params.set_defaults(trace_all_vars=config.trace_all_vars)
    print_params.add_argument('--trace-all-vars', dest='trace_all_vars', action='store_true',
                       help="show all variables in the counterexamples. (Default is \"%s\")"%config.trace_all_vars)

    print_params.set_defaults(full_trace=config.full_trace)
    print_params.add_argument('--full-trace', dest='full_trace', action='store_true',
                       help="sets trace-vars-unchanged and trace-all-vars to True. (Default is \"%s\")"%config.full_trace)
    
    print_params.set_defaults(prefix=None)
    print_params.add_argument('--prefix', metavar='<prefix location>', type=str, required=False,
                       help='write the counterexamples with a specified location prefix.')
    
    print_params.set_defaults(vcd=False)
    print_params.add_argument('--vcd', dest='vcd', action='store_true',
                       help='generate traces also in vcd format.')

    # Translation parameters

    trans_params = parser.add_argument_group('translation')
    
    trans_params.set_defaults(smt2=None)
    trans_params.add_argument('--smt2', metavar='<smt-lib2 file>', type=str, required=False,
                       help='generates the smtlib2 encoding for a BMC call.')

    trans_params.set_defaults(translate=None)
    trans_params.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file.')
    
    printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]

    trans_params.set_defaults(printer=config.printer)
    trans_params.add_argument('--printer', metavar='printer', type=str, nargs='?',
                        help='select the printer between (Default is \"%s\"):\n%s'%(config.printer, "\n".join(printers)))

    trans_params.set_defaults(skip_solving=False)
    trans_params.add_argument('--skip-solving', dest='skip_solving', action='store_true',
                        help='does not call the solver (used with --smt2 or --translate parameters).')

    trans_params.set_defaults(pickle=None)
    trans_params.add_argument('--pickle', metavar='<pickle file>', type=str, required=False,
                       help='pickles the transition system to be loaded later.')

    # Debugging

    deb_params = parser.add_argument_group('verbosity')
    
    deb_params.set_defaults(verbosity=config.verbosity)
    deb_params.add_argument('-v', dest='verbosity', metavar="<integer level>", type=int,
                        help="verbosity level. (Default is \"%s\")"%config.verbosity)

    deb_params.set_defaults(debug=False)
    deb_params.add_argument('--debug', dest='debug', action='store_true',
                       help='enables debug mode.')

    deb_params.set_defaults(time=False)
    deb_params.add_argument('--time', dest='time', action='store_true',
                       help='prints time for every verification.')
    
    args = parser.parse_args()

    config.strfiles = args.input_files
    config.simulate = args.simulate
    config.safety = args.safety
    config.ltl = args.ltl
    config.properties = args.properties
    config.lemmas = args.lemmas
    config.assumptions = args.assumptions
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.fsm_check = args.fsm_check
    config.bmc_length = args.bmc_length
    config.bmc_length_min = args.bmc_length_min
    config.full_trace = args.full_trace
    config.trace_vars_change = args.trace_vars_change
    config.trace_all_vars = args.trace_all_vars
    config.prefix = args.prefix
    config.translate = args.translate
    config.smt2file = args.smt2
    config.strategy = args.strategy
    config.skip_solving = args.skip_solving
    config.pickle_file = args.pickle
    config.abstract_clock = args.abstract_clock
    config.boolean = args.boolean
    config.verbosity = args.verbosity
    config.vcd = args.vcd
    config.prove = args.prove
    config.solver_name = args.solver_name
    config.incremental = not args.ninc
    config.time = args.time
    config.no_clock = args.no_clock
    # config.monitors = args.monitors

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    if args.problems:
        if args.debug:
            sys.exit(run_problems(args.problems, config))
        else:
            try:
                sys.exit(run_problems(args.problems, config))
            except Exception as e:
                Logger.msg(str(e), 0)
                sys.exit(1)

    Logger.error_raise_exept = False
            
    if (args.problems is None) and (args.input_files is None):
        Logger.error("No input files provided")

    if args.printer in [str(x.get_name()) for x in PrintersFactory.get_printers_by_type(PrinterType.TRANSSYS)]:
        config.printer = args.printer
    else:
        Logger.error("Printer \"%s\" not found"%(args.printer))

    if args.strategy not in [s[0] for s in MCConfig.get_strategies()]:
        Logger.error("Strategy \"%s\" not found"%(args.strategy))

    if not(config.simulate or \
           (config.safety) or \
           (config.ltl) or \
           (config.equivalence is not None) or\
           (config.translate is not None) or\
           (config.fsm_check)):
        Logger.error("Analysis selection is necessary")
        
    parsing_defs = [config.properties, config.lemmas, config.assumptions]
    for i in range(len(parsing_defs)):
        if parsing_defs[i] is not None:
            if os.path.isfile(parsing_defs[i]):
                with open(parsing_defs[i]) as f:
                    parsing_defs[i] = [p.strip() for p in f.read().strip().split("\n")]
            else:
                parsing_defs[i] = [p.strip() for p in parsing_defs[i].split(",")]

    [config.properties, config.lemmas, config.assumptions] = parsing_defs

    Logger.error_raise_exept = True
    
    if args.debug:
        sys.exit(run_verification(config))
    else:
        try:
            sys.exit(run_verification(config))
        except Exception as e:
            Logger.msg(str(e), 0)
            sys.exit(1)
   
if __name__ == "__main__":
    main()
            
