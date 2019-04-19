#!/usr/bin/env python3

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
import multiprocessing

from argparse import RawTextHelpFormatter
from textwrap import TextWrapper
from typing import List, NamedTuple, Union

from pysmt.shortcuts import TRUE, FALSE

from cosa.analyzers.dispatcher import ProblemSolver, FILE_SP, MODEL_SP
from cosa.analyzers.mcsolver import MCConfig
from cosa.config import CosaArgParser
from cosa.utils.logger import Logger
from cosa.printers.factory import HTSPrintersFactory
from cosa.printers.template import HTSPrinterType, TraceValuesBase
from cosa.encoders.factory import ModelParsersFactory, GeneratorsFactory, ClockBehaviorsFactory, SyntacticSugarFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.environment import reset_env
from cosa.problem import Problem, Problems, ProblemsManager, Trace, VerificationStatus, VerificationType
from cosa.utils.generic import bold_text

TRACE_PREFIX = "trace"

DEVEL_OPT = "--devel"

class Config(object):
    parser = None
    model_file = None
    verbosity = 1
    devel = False
    bmc_length = 5
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
    trace_values_base = TraceValuesBase.get_all()[0]
    prefix = None
    run_coreir_passes = True
    translate = None
    smt2_tracing = None
    boolean = False
    abstract_clock = False
    add_clock = False
    skip_solving = False
    solver_name = "msat"
    solver_options = {}

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
    opt_circuit = False
    no_arrays = False
    cardinality = 5
    coi = False
    cache_files = False
    clean_cache = False

    printer = None
    strategy = None
    processes = int(multiprocessing.cpu_count()/2)

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
    # TODO: Fix this for the formulae which are not pysmt nodes at this point
    #       accessing the problem copy of it which is still a string
    Logger.log("\nWriting system to \"%s\""%(config.translate), 0)
    printer = HTSPrintersFactory.printer_by_name(config.printer)
    props = []
    if formulae is not None:
        props = [(f.serialize(threshold=100), f, None) for f in formulae if f is not None]
    with open(config.translate, "w") as f:
        f.write(printer.print_hts(hts, props))

def print_problem_result(pbm:NamedTuple,
                         problems_config:ProblemsManager):

    traces = problems_config.get_problem_traces(pbm)
    status = problems_config.get_problem_status(pbm)
    general_config = problems_config.general_config
    count = len(traces) + 1
    if pbm.name is None:
        return (0, [])
    ret_status = 0

    unk_k = "" if status != VerificationStatus.UNK else "\nBMC depth: %s"%pbm.bmc_length
    Logger.log("\n** Problem %s **"%(pbm.name), 0)
    if pbm.description is not None:
        Logger.log("Description: %s"%(pbm.description), 0)
    if pbm.properties is not None:
        Logger.log("Formula: %s"%(pbm.properties), 1)
    Logger.log("Result: %s%s"%(status, unk_k), 0)
    if pbm.verification == VerificationType.PARAMETRIC:
        if pbm.region in [TRUE(),FALSE(),None]:
            Logger.log("Region: %s"%(pbm.region), 0)
        else:
            Logger.log("Region:\n - %s"%(" or \n - ".join([x.serialize(threshold=100) for x in pbm.region])), 0)
    if (pbm.expected is not None):
        expected = VerificationStatus.convert(pbm.expected)
        Logger.log("Expected: %s"%(expected), 0)
        correct = VerificationStatus.compare(VerificationStatus.convert(pbm.expected), status)
        if not correct:
            Logger.log("%s != %s <<<---------| ERROR"%(status, expected), 0)
            ret_status = 1

    assert not(general_config.force_expected and (pbm.expected is None))

    prefix = general_config.prefix
    traces_results = []

    if (traces is not None) and (len(traces) > 0):
        if (pbm.verification == VerificationType.PARAMETRIC) and (status != VerificationStatus.FALSE):
            traces_results = print_traces("Execution", traces, pbm.name, prefix, count)

        if (pbm.verification != VerificationType.SIMULATION) and (status == VerificationStatus.FALSE):
            traces_results = print_traces("Counterexample", traces, pbm.name, prefix, count)

        if (pbm.verification == VerificationType.SIMULATION) and (status == VerificationStatus.TRUE):
            traces_results = print_traces("Execution", traces, pbm.name, prefix, count)

    if general_config.time:
        time = problems_config.get_problem_time(pbm)
        Logger.log("Time: %.2f sec"%(time), 0)

    return (ret_status, traces_results)

# FIXME: replace old version with this
def run_problems_new(problems_config:ProblemsManager):

    if sys.version_info[0] < 3:
        if config.devel:
            Logger.warning("This software is not tested for Python 2, we recommend to use Python 3 instead")
        else:
            Logger.error("This software is not tested for Python 2, please use Python 3 instead. To avoid this error run in developer mode")

    reset_env()

    # Named tuple representing all the general configuration options
    # (things that don't change between problems)
    general_config = problems_config.general_config
    Logger.verbosity = general_config.verbosity
    Logger.time = general_config.time

    psol = ProblemSolver()
    psol.solve_problems_new(problems_config)

    global_status = 0
    traces = []

    if len(problems_config.problems) > 0:
        Logger.log("\n*** SUMMARY ***", 0)
    else:
        if not general_config.translate:
            Logger.log("No problems to solve", 0)
            return 0

    # TODO: Enable all this
    formulae = []
    for pbm in problems_config.problems:
        (status, trace) = print_problem_result(pbm,
                                               problems_config)

        if status != 0:
            global_status = status
        traces += trace
        formulae.append(pbm.properties)

    if len(traces) > 0:
        Logger.log("\n*** TRACES ***\n", 0)
        for trace in traces:
            Logger.log("[%d]:\t%s"%(traces.index(trace)+1, trace), 0)

    if general_config.translate:
        translate(problems_config.hts, general_config, formulae)

    if global_status != 0:
        Logger.log("", 0)
        Logger.warning("Verifications with unexpected result")

    return global_status


def run_problems(problems_file, config, problems=None):

    if sys.version_info[0] < 3:
        if config.devel:
            Logger.warning("This software is not tested for Python 2, we recommend to use Python 3 instead")
        else:
            Logger.error("This software is not tested for Python 2, please use Python 3 instead. To avoid this error run in developer mode")

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
        formulae.append(pbm.properties)

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
    problems.model_file = config.model_file
    problems.prefix = config.prefix
    problems.prove = config.prove
    problems.skip_solving = config.skip_solving
    problems.smt2_tracing = config.smt2_tracing
    problems.solver_name = config.solver_name
    problems.strategy = config.strategy
    problems.symbolic_init = config.symbolic_init
    problems.zero_init = config.zero_init
    problems.time = config.time
    problems.trace_all_vars = config.trace_all_vars
    problems.trace_values_base = config.trace_values_base
    problems.trace_vars_change = config.trace_vars_change
    problems.vcd = config.vcd
    problems.verbosity = config.verbosity
    problems.boolean = config.boolean
    problems.add_clock = config.add_clock
    problems.abstract_clock = config.abstract_clock
    problems.run_coreir_passes = config.run_coreir_passes
    problems.opt_circuit = config.opt_circuit
    problems.no_arrays = config.no_arrays
    problems.relative_path = "./"

    problem = problems.new_problem()

    if config.safety:
        problem.verification = VerificationType.SAFETY
    elif config.ltl:
        problem.verification = VerificationType.LTL
    elif config.equivalence is not None:
        problem.verification = VerificationType.EQUIVALENCE
        problem.equivalence = config.equivalence
        problems.equivalence = config.equivalence
    elif config.simulate:
        problem.verification = VerificationType.SIMULATION
    elif config.parametric:
        problem.verification = VerificationType.PARAMETRIC
    elif config.fsm_check:
        problem.verification = VerificationType.EQUIVALENCE
        problem.equivalence = config.model_file

    if not problem.verification == VerificationType.EQUIVALENCE:
        problem.formula = config.properties

    problem.name = problem.verification

    if problem.formula or problem.verification:
        problems.add_problem(problem)

    return run_problems(None, config, problems)

def main():
    wrapper = TextWrapper(initial_indent=" - ")
    extra_info = []

    devel = False
    if DEVEL_OPT in sys.argv:
        sys.argv = [a for a in sys.argv if a != DEVEL_OPT]
        devel = True

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
        generators.append("\n".join(wrapper.wrap("\"%s\": %s, parameters (%s) values (%s)"%(x.get_name(), x.get_desc(), x.get_interface(), x.get_values()))))

    extra_info.append('\nModule generators:\n%s'%("\n".join(generators)))

    modifiers = []
    modifiers.append(" - \"None\": No extension")
    for x in ModelModifiersFactory.get_modifiers():
        wrapper.subsequent_indent = " "*(len(" - \"\": "+x.get_name()))
        modifiers.append("\n".join(wrapper.wrap("\"%s\": %s"%(x.get_name(), x.get_desc()))))

    extra_info.append('\nModel modifiers:\n%s'%("\n".join(modifiers)))


    parser = CosaArgParser(description=bold_text('CoSA: CoreIR Symbolic Analyzer\n..an SMT-based Symbolic Model Checker for Hardware Design'),
                           formatter_class=RawTextHelpFormatter,
                           epilog="\n".join(extra_info))


    # Main inputs

    # Options in the general group are options that must stay constant for all problems
    # in a problem file

    # in our architecture, the input files are compiled into a single transition system which
    # is then used to verify mutliple properties (problems)
    # thus any option regarding the encoding of said transition system must be a general option

    in_options = parser.add_general_group('input options')

    av_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                      for x in ModelParsersFactory.get_parsers() if x.is_available()]

    ua_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                      for x in ModelParsersFactory.get_parsers() if not x.is_available()]

    in_options.set_defaults(model_file=None)
    in_options.add_argument('-i', '--model_file', metavar='<model files>', type=str, required=False,
                            help='comma separated list of input files.\nSupported types:\n%s%s'%\
                            ("\n".join(av_input_types), "\nNot enabled:\n%s"%("\n".join(ua_input_types)) \
                             if len(ua_input_types) > 0 else ""))

    in_options.set_defaults(problems=None)
    in_options.add_argument('--problems', metavar='<problems file>', type=str, required=False,
                            help='problems file describing the verifications to be performed.',
                            is_config_file=True)

    general_solving_options = parser.add_general_group('solving')

    general_solving_options.set_defaults(assume_if_true=False)
    general_solving_options.add_argument('--assume-if-true', dest='assume_if_true', action='store_true',
                            help="add true properties as assumptions. (Default is \"%s\")"%False)

    general_encoding_options = parser.add_general_group('encoding')

    general_encoding_options.set_defaults(abstract_clock=False)
    general_encoding_options.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                                          help="abstracts the clock behavior. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(add_clock=False)
    general_encoding_options.add_argument('--add-clock', dest='add_clock', action='store_true',
                                          help="adds clock behavior. (Default is \"%s\")"%False)

    # TODO: Deprecate this
    general_encoding_options.set_defaults(boolean=False)
    general_encoding_options.add_argument('--boolean', dest='boolean', action='store_true',
                                          help='interprets single bits as Booleans instead of 1-bit Bitvector. (Default is \"%s\")'%False)

    general_encoding_options.set_defaults(cache_files=False)
    general_encoding_options.add_argument('-c', '--cache-files', dest='cache_files', action='store_true',
                                          help="caches encoded files to speed-up parsing. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(clean_cache=False)
    general_encoding_options.add_argument('--clean-cache', dest='clean_cache', action='store_true',
                                          help="deletes the stored cache. (Default is \"%s\")"%False)

    general_encoding_options.add_argument('--clock-behaviors', metavar='clock_behaviors', type=str, nargs='?',
                                          help='semi column separated list of clock behaviors instantiation.')

    general_encoding_options.set_defaults(default_initial_value=None)
    general_encoding_options.add_argument('--default-initial-value',
                                          help='Set uninitialized bits to 0 or 1.')

    general_encoding_options.set_defaults(model_extension=None)
    general_encoding_options.add_argument('--model-extension', metavar='model_extension', type=str, nargs='?',
                            help='select the model modifier. (Default is \"%s\")'%(None))

    general_encoding_options.set_defaults(no_arrays=False)
    general_encoding_options.add_argument('--no-arrays', action='store_true',
                            help='For Yosys frontend, blast memories to registers instead of using arrays.\n'
                            'Note: This can fail -- particularly for dualport memories.')

    general_encoding_options.set_defaults(opt_circuit=False)
    general_encoding_options.add_argument('--opt-circuit', action='store_true',
                            help='Use Yosys to optimize the circuit -- can remove signals.')

    general_encoding_options.set_defaults(run_coreir_passes=True)
    general_encoding_options.add_argument('--no-run-coreir-passes', dest='run_coreir_passes', action='store_false',
                                          help='does not run CoreIR passes. (Default is \"%s\")'%True)

    general_encoding_options.set_defaults(symbolic_init=False)
    general_encoding_options.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                                          help='removes constraints on the initial state. (Default is \"%s\")'%False)

    general_encoding_options.set_defaults(vcd=False)
    general_encoding_options.add_argument('--vcd', dest='vcd', action='store_true',
                                          help="generate traces also in vcd format. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(zero_init=False)
    general_encoding_options.add_argument('--zero-init', dest='zero_init', action='store_true',
                                          help='sets initial state to zero. (Default is \"%s\")'%False)

    # General results options
    general_results_options = parser.add_general_group('results')

    general_results_options.set_defaults(force_expected=False)
    general_results_options.add_argument('--force-expected', action='store_true',
                                         help='Force the result to be the provided expected value')

    # Problem-specific processing options
    problem_processing_options = parser.add_problem_group('problem processing')
    problem_processing_options.set_defaults(simplify=True)
    problem_processing_options.add_argument('--simplify', action='store_true',
                                            help='simplify formulae with pysmt. (Default is \"%s\")'%True)

    # Verification Options

    ver_options = parser.add_problem_group('analysis')
    verification_choices = [
        VerificationType.SAFETY,
        VerificationType.LIVENESS,
        VerificationType.EVENTUALLY,
        VerificationType.DETERMINISTIC,
        VerificationType.SIMULATION,
        VerificationType.LTL,
        VerificationType.PARAMETRIC
                             ]
    ver_options.set_defaults(verification=None)
    ver_options.add_argument('--verification', type=str,
                             choices=verification_choices,
                             help="Choose the verification type from: {}"
                             "".format("\n".join("\t%s"%v for v in verification_choices)))
    # TODO clean this up
    # ver_options.set_defaults(safety=False)
    # ver_options.add_argument('--safety', dest='safety', action='store_true',
    #                    help='safety verification using BMC.')

    # ver_options.set_defaults(ltl=False)
    # ver_options.add_argument('--ltl', dest='ltl', action='store_true',
    #                    help='ltl verification using BMC.')

    # ver_options.set_defaults(simulate=False)
    # ver_options.add_argument('--simulate', dest='simulate', action='store_true',
    #                    help='simulate system using BMC.')

    # ver_options.set_defaults(equivalence=None)
    # ver_options.add_argument('--equivalence', metavar='<input files>', type=str, required=False,
    #                    help='equivalence checking using BMC.')

    # ver_options.set_defaults(fsm_check=False)
    # ver_options.add_argument('--fsm-check', dest='fsm_check', action='store_true',
    #                    help='check if the state machine is deterministic.')

    # ver_options.set_defaults(parametric=False)
    # ver_options.add_argument('--parametric', dest='parametric', action='store_true',
    #                    help='parametric analysis using BMC.')

    # Verification parameters

    ver_params = parser.add_problem_group('verification parameters')

    ver_params.set_defaults(expected=None)
    ver_params.add_argument('--expected', required=False, type=str,
                            help='Expected verification result')

    ver_params.set_defaults(properties=None)
    ver_params.add_argument('-p', '--properties', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of properties.')

    ver_params.set_defaults(bmc_length=5)
    ver_params.add_argument('-k', '--bmc-length', metavar='<BMC length>', type=int, required=False,
                            help="depth of BMC unrolling. (Default is \"%s\")"%5)

    ver_params.set_defaults(bmc_length_min=0)
    ver_params.add_argument('-km', '--bmc-length-min', metavar='<BMC length>', type=int, required=False,
                        help="minimum depth of BMC unrolling. (Default is \"%s\")"%0)

    ver_params.set_defaults(precondition=None)
    ver_params.add_argument('-r', '--precondition', metavar='<invar>', type=str, required=False,
                       help='invariant properties precondition.')

    ver_params.set_defaults(lemmas=None)
    ver_params.add_argument('-l', '--lemmas', metavar='<invar list>', type=str, required=False,
                       help='comma separated list of lemmas.')

    ver_params.set_defaults(assumptions=None)
    ver_params.add_argument('-a', '--assumptions', metavar='<invar assumptions list>', type=str, required=False,
                       help='semi column separated list of invariant assumptions.')

    ver_params.add_argument('--generators', metavar='generators', type=str, nargs='?',
                        help='semi column separated list of generators instantiation.')

    ver_params.set_defaults(prove=False)
    ver_params.add_argument('--prove', dest='prove', action='store_true',
                            help="use indution to prove the satisfiability of the property. (Default is \"%s\")"%False)

    ver_params.set_defaults(coi=False)
    ver_params.add_argument('--coi', dest='coi', action='store_true',
                            help="enables Cone of Influence. (Default is \"%s\")"%False)

    ver_params.set_defaults(cardinality=5)
    ver_params.add_argument('--cardinality', dest='cardinality', type=int, required=False,
                            help="bounds number of active parameters. -1 is unbounded. (Default is \"%s\")"%5)

    strategies = [" - \"%s\": %s"%(x[0], x[1]) for x in MCConfig.get_strategies()]
    defstrategy = MCConfig.get_strategies()[0][0]
    ver_params.set_defaults(strategy=defstrategy)
    ver_params.add_argument('--strategy', metavar='strategy', type=str, nargs='?',
                        help='select the BMC strategy between (Default is \"%s\"):\n%s'%(defstrategy, "\n".join(strategies)))

    ver_params.set_defaults(processes=int(multiprocessing.cpu_count()/2))
    ver_params.add_argument('-j', dest='processes', metavar="<integer level>", type=int,
                            help="number of multi-processes for MULTI strategy. (Default is \"%s\")"%int(multiprocessing.cpu_count()/2))

    ver_params.set_defaults(incremental=True)
    ver_params.add_argument('--incremental', action='store_true',
                            help="disables incrementality. (Default is \"%s\")"%True)

    ver_params.set_defaults(solver_name='msat')
    ver_params.add_argument('--solver-name', metavar='<Solver Name>', type=str, required=False,
                        help="name of SMT solver to be use. (Default is \"%s\")"%'msat')

    # General printing parameters

    print_params = parser.add_general_group('trace printing')

    print_params.set_defaults(trace_vars_change=False)
    print_params.add_argument('--trace-vars-change', dest='trace_vars_change', action='store_true',
                              help="show variable assignments in the counterexamples even when unchanged. (Default is \"%s\")"%False)

    print_params.set_defaults(trace_all_vars=False)
    print_params.add_argument('--trace-all-vars', dest='trace_all_vars', action='store_true',
                              help="show all variables in the counterexamples. (Default is \"%s\")"%False)

    print_params.set_defaults(full_trace=False)
    print_params.add_argument('--full-trace', dest='full_trace', action='store_true',
                              help="sets trace-vars-unchanged and trace-all-vars to True. (Default is \"%s\")"%False)

    trace_values_base_default = TraceValuesBase.get_all()[0]
    print_params.set_defaults(trace_values_base=trace_values_base_default)
    print_params.add_argument('--trace-values-base', metavar='trace_values_base', type=str, nargs='?',
                              help="sets the style of Bit-Vector values printing. (Default is \"%s\")"%trace_values_base_default)

    print_params.set_defaults(prefix=None)
    print_params.add_argument('--prefix', metavar='<prefix location>', type=str, required=False,
                       help='write the counterexamples with a specified location prefix.')

    # General translation parameters
    general_trans_params = parser.add_general_group('translation')

    general_trans_params.set_defaults(translate=None)
    general_trans_params.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file.')


    # Problem-specific translation parameters

    trans_params = parser.add_problem_group('translation')
    printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in HTSPrintersFactory.get_printers_by_type(HTSPrinterType.TRANSSYS)]

    printer_default = HTSPrintersFactory.get_default().get_name()
    trans_params.set_defaults(printer=printer_default)
    trans_params.add_argument('--printer', metavar='printer', type=str, nargs='?',
                        help='select the printer between (Default is \"%s\"):\n%s'%(printer_default, "\n".join(printers)))

    trans_params.set_defaults(skip_solving=False)
    trans_params.add_argument('--skip-solving', dest='skip_solving', action='store_true',
                              help="does not call the solver. (Default is \"%s\")"%False)

    # Debugging

    deb_params = parser.add_general_group('verbosity')

    deb_params.set_defaults(verbosity=1)
    deb_params.add_argument('-v', dest='verbosity', metavar="<integer level>", type=int,
                            help="verbosity level. (Default is \"%s\")"%1)

    deb_params.set_defaults(time=False)
    deb_params.add_argument('--time', dest='time', action='store_true',
                            help="prints time for every verification. (Default is \"%s\")"%False)

    deb_params.set_defaults(devel=False)
    deb_params.add_argument('--devel', dest='devel', action='store_true',
                            help="enables developer mode. (Default is \"%s\")"%False)


    # Meta Options
    # these cannot be set by the command line, and are instead just set internally
    meta_options = parser.add_problem_group('meta')
    meta_options.set_defaults(name='EMBEDDED')
    meta_options.add_argument('--name', type=str, help=argparse.SUPPRESS)

    meta_options.set_defaults(description='EMBEDDED')
    meta_options.add_argument('--description', type=str, help=argparse.SUPPRESS)

    # Developers
    # Options are suppressed from help menu if help called without --devel option
    devel_params = parser.add_problem_group('developer')
    devel_params.set_defaults(smt2_tracing=None)
    devel_params.add_argument('--smt2-tracing', metavar='<smt-lib2 file>', type=str, required=False,
                              help='generates the smtlib2 tracing file for '
                              'each solver call.' if not devel else argparse.SUPPRESS)

    devel_params.set_defaults(solver_options=None)
    devel_params.add_argument('--solver-options', metavar='[key:value options]', type=str, required=False,
                              help='space delimited key:value pairs '
                              'to set specific SMT solver options (EXPERTS ONLY)' if not devel else argparse.SUPPRESS)


    problems_config = parser.parse_args()

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    sys.exit(run_problems_new(problems_config))

    # if args.printer in [str(x.get_name()) for x in HTSPrintersFactory.get_printers_by_type(HTSPrinterType.TRANSSYS)]:
    #     config.printer = args.printer
    # else:
    #     Logger.error("Printer \"%s\" not found"%(args.printer))

    # if args.problems:
    #     if config.devel:
    #         sys.exit(run_problems(args.problems, config))
    #     else:
    #         try:
    #             sys.exit(run_problems(args.problems, config))
    #         except Exception as e:
    #             Logger.error(str(e), False)
    #             sys.exit(1)

    # Logger.error_raise_exept = False

    # if (args.problems is None) and (args.model_file is None):
    #     Logger.error("No input files provided")

    # if args.strategy not in [s[0] for s in MCConfig.get_strategies()]:
    #     Logger.error("Strategy \"%s\" not found"%(args.strategy))

    # if not(config.simulate or \
    #        (config.safety) or \
    #        (config.parametric) or \
    #        (config.ltl) or \
    #        (config.equivalence is not None) or\
    #        (config.translate is not None) or\
    #        (config.fsm_check)):
    #     Logger.error("Analysis selection is necessary")

    # Logger.error_raise_exept = True

    # if config.devel:
    #     sys.exit(run_verification(config))
    # else:
    #     try:
    #         sys.exit(run_verification(config))
    #     except Exception as e:
    #         Logger.error(str(e), False)
    #         sys.exit(1)

if __name__ == "__main__":
    main()
