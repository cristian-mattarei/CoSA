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

from textwrap import TextWrapper
from argparse import RawTextHelpFormatter

from pysmt.shortcuts import TRUE, FALSE

from cosa.analyzers.dispatcher import ProblemSolver, FILE_SP, MODEL_SP
from cosa.analyzers.mcsolver import MCConfig
from cosa.utils.logger import Logger
from cosa.printers.factory import HTSPrintersFactory
from cosa.printers.template import HTSPrinterType
from cosa.encoders.factory import ModelParsersFactory, GeneratorsFactory, ClockBehaviorsFactory, SyntacticSugarFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.environment import reset_env
from cosa.problem import Problem, Problems, VerificationStatus, VerificationType
from cosa.utils.generic import bold_text

TRACE_PREFIX = "trace"

class Config(object):
    parser = None
    strfiles = None
    verbosity = 1
    debug = False
    bmc_length = 10
    bmc_length_min = 0
    
    simulate = False
    safety = None
    parametric = None
    ltl = None
    equivalence = None
    problems = None
    
    properties = None
    lemmas = None
    precondition = None
    assumptions = None
    symbolic_init = False
    zero_init = False
    fsm_check = False
    full_trace = False
    trace_vars_change = False
    trace_all_vars = False
    prefix = None
    run_passes = True
    translate = None
    smt2file = None
    boolean = False
    abstract_clock = False
    add_clock = False
    skip_solving = False
    solver_name = "msat"
    vcd = False
    prove = False
    incremental = True
    deterministic = False
    time = False
    generators = None
    clock_behaviors = None
    force_expected = False
    assume_if_true = False
    model_extension = None
    cardinality = 5

    printer = None
    strategy = None
    
    def __init__(self):
        HTSPrintersFactory.init_printers()
        
        self.printer = HTSPrintersFactory.get_default().get_name()
        self.strategy = MCConfig.get_strategies()[0][0]
        
def traces_printed(msg, trace_files):
    traces = ", and\n - ".join(["\"%s\""%f for f in trace_files])
    Logger.log("\n%s saved in:\n - %s"%(msg, traces), 0)
    
def print_traces(msg, traces, index, prefix, tracecount):
    trace_files = []
    trace_prefix = None

    i = 1
    for trace in traces:
        if prefix:
            trace_prefix = prefix
        else:
            if not trace.human_readable:
                trace_prefix = TRACE_PREFIX
        
        if trace_prefix:
            trace_file = "%s[%d]-%s.%s"%(trace_prefix, i, index, trace.extension)
            i+=1
            trace_files.append(trace_file)
            with open(trace_file, "w") as f:
                f.write(str(trace))

            if tracecount < 0:
                continue

        else:
            Logger.log("%s:"%(msg), 0)
            Logger.log(str(trace), 0)

    if (tracecount > 0) and (len(trace_files) > 0):
        traces_idx = ", ".join("[%s]"%(idx) for idx in range(tracecount, tracecount+len(traces), 1))
        Logger.log("%s%s: %s"%(msg, "s" if len(traces) > 1 else "", traces_idx), 0)
        tracelen = max(t.length for t in traces)
        Logger.log("Trace%s: %d"%("s (max) length" if len(traces) > 1 else " length", tracelen+1), 0)
            
    if (tracecount < 0) and (len(trace_files) > 0):
        traces_printed(msg, trace_files)
        return []
    
    return trace_files

def get_file_flags(strfile):
    if "[" not in strfile:
        return (strfile, [])
    
    (strfile, flags) = (strfile[:strfile.index("[")], strfile[strfile.index("[")+1:strfile.index("]")].split(FILE_SP))
    return (strfile, flags)

def translate(hts, config, formulae=None):
    Logger.log("\nWriting system to \"%s\""%(config.translate), 0)
    printer = HTSPrintersFactory.printer_by_name(config.printer)
    props = []
    if formulae is not None:
        props = [(f.serialize(threshold=100), f, None) for f in formulae if f is not None]
    with open(config.translate, "w") as f:
        f.write(printer.print_hts(hts, props))

def print_problem_result(pbm, config, count=-1):
    if pbm.name is None:
        return (0, [])
    ret_status = 0

    unk_k = "" if pbm.status != VerificationStatus.UNK else "\nBMC depth: %s"%pbm.bmc_length
    Logger.log("\n** Problem %s **"%(pbm.name), 0)
    if pbm.description is not None:
        Logger.log("Description: %s"%(pbm.description), 0)
    if pbm.formula is not None:
        Logger.log("Formula: %s"%(pbm.formula.serialize(threshold=100)), 1)
    Logger.log("Result: %s%s"%(pbm.status, unk_k), 0)
    if pbm.verification == VerificationType.PARAMETRIC:
        if pbm.region in [TRUE(),FALSE(),None]:
            Logger.log("Region: %s"%(pbm.region), 0)
        else:
            Logger.log("Region:\n - %s"%(" or \n - ".join([x.serialize(threshold=100) for x in pbm.region])), 0)
    if (pbm.expected is not None):
        expected = VerificationStatus.convert(pbm.expected)
        Logger.log("Expected: %s"%(expected), 0)
        correct = VerificationStatus.compare(VerificationStatus.convert(pbm.expected), pbm.status)
        if not correct:
            Logger.log("%s != %s <<<---------| ERROR"%(pbm.status, expected), 0)
            ret_status = 1

    assert not(config.force_expected and (pbm.expected is None))

    prefix = config.prefix if config.prefix is not None else pbm.trace_prefix

    traces = []

    if (pbm.traces is not None) and (len(pbm.traces) > 0):
        if (pbm.verification == VerificationType.PARAMETRIC) and (pbm.status != VerificationStatus.FALSE):
            traces = print_traces("Execution", pbm.traces, pbm.name, prefix, count)

        if (pbm.verification != VerificationType.SIMULATION) and (pbm.status == VerificationStatus.FALSE):
            traces = print_traces("Counterexample", pbm.traces, pbm.name, prefix, count)

        if (pbm.verification == VerificationType.SIMULATION) and (pbm.status == VerificationStatus.TRUE):
            traces = print_traces("Execution", pbm.traces, pbm.name, prefix, count)

    if pbm.time:
        Logger.log("Time: %.2f sec"%(pbm.time), 0)

    return (ret_status, traces)

def run_problems(problems_file, config, problems=None):
    
    if sys.version_info[0] < 3:
        if config.debug:
            Logger.warning("This software is not tested for Python 2, we recommend to use Python 3 instead")
        else:
            Logger.error("This software is not tested for Python 2, please use Python 3 instead. To avoid this error run in debug mode")

    reset_env()
    Logger.verbosity = config.verbosity
    Logger.time = config.time
    
    psol = ProblemSolver()
    if problems is None:
        problems = Problems()
        problems.load_problems(problems_file)
        
    psol.solve_problems(problems, config)

    global_status = 0
    traces = []

    if len(problems.problems) > 0:
        Logger.log("\n*** SUMMARY ***", 0)
    else:
        if not config.translate:
            Logger.log("No problems to solve", 0)
            return 0

    formulae = []
    for pbm in problems.problems:
        (status, trace) = print_problem_result(pbm, config, len(traces)+1)
        if status != 0:
            global_status = status
        traces += trace
        formulae.append(pbm.formula)

    if len(traces) > 0:
        Logger.log("\n*** TRACES ***\n", 0)
        for trace in traces:
            Logger.log("[%d]:\t%s"%(traces.index(trace)+1, trace), 0)

    if config.translate:
        translate(problems.get_hts(), config, formulae)

    if global_status != 0:
        Logger.log("", 0)
        Logger.warning("Verifications with unexpected result")
        
    return global_status

def run_verification(config):
    reset_env()
    Logger.verbosity = config.verbosity

    problems = Problems()
        
    problems.assumptions = config.assumptions
    problems.bmc_length = config.bmc_length
    problems.bmc_length_min = config.bmc_length_min
    problems.full_trace = config.full_trace
    problems.generators = config.generators
    problems.clock_behaviors = config.clock_behaviors
    problems.incremental = config.incremental
    problems.lemmas = config.lemmas
    problems.model_file = config.strfiles
    problems.prefix = config.prefix
    problems.prove = config.prove
    problems.skip_solving = config.skip_solving
    problems.smt2_tracing = config.smt2file
    problems.solver_name = config.solver_name
    problems.strategy = config.strategy
    problems.symbolic_init = config.symbolic_init
    problems.zero_init = config.zero_init
    problems.time = config.time
    problems.trace_all_vars = config.trace_all_vars
    problems.trace_vars_change = config.trace_vars_change
    problems.vcd = config.vcd
    problems.verbosity = config.verbosity
    
    problems.model_file = config.strfiles
    problems.boolean = config.boolean
    problems.add_clock = config.add_clock
    problems.abstract_clock = config.abstract_clock
    problems.run_coreir_passes = config.run_passes
    problems.relative_path = "./"

    problem = problems.new_problem()

    if config.safety:
        problem.verification = VerificationType.SAFETY
    elif config.ltl:
        problem.verification = VerificationType.LTL
    elif config.equivalence is not None:
        problem.verification = VerificationType.EQUIVALENCE
        problem.equivalence = config.equivalence
    elif config.simulate:
        problem.verification = VerificationType.SIMULATION
    elif config.parametric:
        problem.verification = VerificationType.PARAMETRIC
    elif config.fsm_check:
        problem.verification = VerificationType.EQUIVALENCE
        problem.equivalence = config.strfiles

    if not problem.verification == VerificationType.EQUIVALENCE:
        problem.formula = config.properties

    problem.name = VerificationType.to_string(problem.verification)
    
    if problem.formula or problem.verification:
        problems.add_problem(problem)

    return run_problems(None, config, problems)
            
def main():
    wrapper = TextWrapper(initial_indent=" - ")
    extra_info = []

    extra_info.append(bold_text("\nADDITIONAL INFORMATION:"))
    
    clock_behaviors = []
    for x in ClockBehaviorsFactory.get_clockbehaviors():
        wrapper.subsequent_indent = " "*(len(" - \"\": "+x.get_name()))
        clock_behaviors.append("\n".join(wrapper.wrap("\"%s\": %s, parameters (%s)"%(x.get_name(), x.get_desc(), x.get_interface()))))

    extra_info.append('\nClock behaviors:\n%s'%("\n".join(clock_behaviors)))


    sugars = []
    for x in SyntacticSugarFactory.get_sugars():
        wrapper.subsequent_indent = " "*(len(" - \"\": "+x.get_name()))
        sugars.append("\n".join(wrapper.wrap("\"%s\": %s, parameters (%s)"%(x.get_name(), x.get_desc(), x.get_interface()))))
    

    extra_info.append('\nSpecial operators:\n%s'%("\n".join(sugars)))

    generators = []
    for x in GeneratorsFactory.get_generators():
        wrapper.subsequent_indent = " "*(len(" - \"\": "+x.get_name()))
        generators.append("\n".join(wrapper.wrap("\"%s\": %s, parameters (%s)"%(x.get_name(), x.get_desc(), x.get_interface()))))
    
    extra_info.append('\nModule generators:\n%s'%("\n".join(generators)))

    modifiers = []
    modifiers.append(" - \"None\": No extension")
    for x in ModelModifiersFactory.get_modifiers():
        wrapper.subsequent_indent = " "*(len(" - \"\": "+x.get_name()))
        modifiers.append("\n".join(wrapper.wrap("\"%s\": %s"%(x.get_name(), x.get_desc()))))
    
    extra_info.append('\nModel modifiers:\n%s'%("\n".join(modifiers)))
    
    parser = argparse.ArgumentParser(description=bold_text('CoSA: CoreIR Symbolic Analyzer\n..an SMT-based Symbolic Model Checker for Hardware Design'), \
                                     #usage='%(prog)s [options]', \
                                     formatter_class=RawTextHelpFormatter, \
                                     epilog="\n".join(extra_info))

    config = Config()

    # Main inputs

    in_options = parser.add_argument_group('input options')

    av_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                      for x in ModelParsersFactory.get_parsers() if x.is_available()]

    ua_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                      for x in ModelParsersFactory.get_parsers() if not x.is_available()]
    
    in_options.set_defaults(input_files=None)
    in_options.add_argument('-i', '--input_files', metavar='<input files>', type=str, required=False,
                            help='comma separated list of input files.\nSupported types:\n%s%s'%\
                            ("\n".join(av_input_types), "\nNot enabled:\n%s"%("\n".join(ua_input_types)) \
                             if len(ua_input_types) > 0 else ""))
    
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

    ver_options.set_defaults(parametric=False)
    ver_options.add_argument('--parametric', dest='parametric', action='store_true',
                       help='parametric analysis using BMC.')
    
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

    ver_params.set_defaults(precondition=None)
    ver_params.add_argument('-c', '--precondition', metavar='<invar>', type=str, required=False,
                       help='invariant properties precondition.')
    
    ver_params.set_defaults(lemmas=None)
    ver_params.add_argument('-l', '--lemmas', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of lemmas.')

    ver_params.set_defaults(assumptions=None)
    ver_params.add_argument('-a', '--assumptions', metavar='<invar assumptions list>', type=str, required=False,
                       help='semi column separated list of invariant assumptions.')

    ver_params.add_argument('--generators', metavar='generators', type=str, nargs='?',
                        help='semi column separated list of generators instantiation.')

    ver_params.add_argument('--clock-behaviors', metavar='clock_behaviors', type=str, nargs='?',
                        help='semi column separated list of clock behaviors instantiation.')
    
    ver_params.set_defaults(prove=False)
    ver_params.add_argument('--prove', dest='prove', action='store_true',
                       help='use indution to prove the satisfiability of the property.')

    ver_params.set_defaults(assume_if_true=False)
    ver_params.add_argument('--assume-if-true', dest='assume_if_true', action='store_true',
                       help='add true properties as assumptions.')

    ver_params.set_defaults(cardinality=config.cardinality)
    ver_params.add_argument('--cardinality', dest='cardinality', type=int, required=False,
                       help="bounds number of active parameters. -1 is unbounded. (Default is \"%s\")"%config.cardinality)
    
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

    enc_params.set_defaults(add_clock=False)
    enc_params.add_argument('--add-clock', dest='add_clock', action='store_true',
                       help='adds clock behavior.')
    
    enc_params.set_defaults(abstract_clock=False)
    enc_params.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                       help='abstracts the clock behavior.')

    enc_params.set_defaults(symbolic_init=config.symbolic_init)
    enc_params.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                       help='removes constraints on the initial state. (Default is \"%s\")'%config.symbolic_init)

    enc_params.set_defaults(zero_init=config.zero_init)
    enc_params.add_argument('--zero-init', dest='zero_init', action='store_true',
                       help='sets initial state to zero. (Default is \"%s\")'%config.zero_init)
    
    enc_params.set_defaults(boolean=config.boolean)
    enc_params.add_argument('--boolean', dest='boolean', action='store_true',
                        help='interprets single bits as Booleans instead of 1-bit Bitvector. (Default is \"%s\")'%config.boolean)

    enc_params.set_defaults(run_passes=config.run_passes)
    enc_params.add_argument('--no-run-passes', dest='run_passes', action='store_false',
                        help='does not run CoreIR passes. (Default is \"%s\")'%config.run_passes)

    enc_params.set_defaults(model_extension=config.model_extension)
    enc_params.add_argument('--model-extension', metavar='model_extension', type=str, nargs='?',
                            help='select the model modifier. (Default is \"%s\")'%(config.model_extension))
    
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
    
    printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in HTSPrintersFactory.get_printers_by_type(HTSPrinterType.TRANSSYS)]

    trans_params.set_defaults(printer=config.printer)
    trans_params.add_argument('--printer', metavar='printer', type=str, nargs='?',
                        help='select the printer between (Default is \"%s\"):\n%s'%(config.printer, "\n".join(printers)))

    trans_params.set_defaults(skip_solving=False)
    trans_params.add_argument('--skip-solving', dest='skip_solving', action='store_true',
                        help='does not call the solver (used with --smt2 or --translate parameters).')

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
    config.parametric = args.parametric
    config.ltl = args.ltl
    config.properties = args.properties
    config.lemmas = args.lemmas
    config.precondition = args.precondition
    config.assumptions = args.assumptions
    config.equivalence = args.equivalence
    config.symbolic_init = args.symbolic_init
    config.zero_init = args.zero_init
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
    config.abstract_clock = args.abstract_clock
    config.boolean = args.boolean
    config.verbosity = args.verbosity
    config.vcd = args.vcd
    config.prove = args.prove
    config.solver_name = args.solver_name
    config.incremental = not args.ninc
    config.time = args.time
    config.add_clock = args.add_clock
    config.generators = args.generators
    config.clock_behaviors = args.clock_behaviors
    config.assume_if_true = args.assume_if_true
    config.model_extension = args.model_extension
    config.cardinality = args.cardinality
    config.debug = args.debug

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    if args.printer in [str(x.get_name()) for x in HTSPrintersFactory.get_printers_by_type(HTSPrinterType.TRANSSYS)]:
        config.printer = args.printer
    else:
        Logger.error("Printer \"%s\" not found"%(args.printer))
        
    if args.problems:
        if args.debug:
            sys.exit(run_problems(args.problems, config))
        else:
            try:
                sys.exit(run_problems(args.problems, config))
            except Exception as e:
                Logger.error(str(e), False)
                sys.exit(1)

    Logger.error_raise_exept = False
            
    if (args.problems is None) and (args.input_files is None):
        Logger.error("No input files provided")

    if args.strategy not in [s[0] for s in MCConfig.get_strategies()]:
        Logger.error("Strategy \"%s\" not found"%(args.strategy))

    if not(config.simulate or \
           (config.safety) or \
           (config.parametric) or \
           (config.ltl) or \
           (config.equivalence is not None) or\
           (config.translate is not None) or\
           (config.fsm_check)):
        Logger.error("Analysis selection is necessary")

    Logger.error_raise_exept = True
    
    if args.debug:
        sys.exit(run_verification(config))
    else:
        try:
            sys.exit(run_verification(config))
        except Exception as e:
            Logger.error(str(e), False)
            sys.exit(1)

if __name__ == "__main__":
    main()
            
