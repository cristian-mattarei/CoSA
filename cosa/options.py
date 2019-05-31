# Copyright 2018 Stanford University
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import argparse
from argparse import RawTextHelpFormatter
import multiprocessing
import sys
from textwrap import TextWrapper

from cosa.analyzers.mcsolver import get_verification_strategies
from cosa.config import CosaArgParser
from cosa.encoders.factory import ModelParsersFactory, GeneratorsFactory, ClockBehaviorsFactory, SyntacticSugarFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.problem import VerificationType
from cosa.printers.template import HTSPrinterType, TraceValuesBase
from cosa.printers.factory import HTSPrintersFactory
from cosa.utils.generic import bold_text

__all__ = ['cosa_option_manager']

DEVEL_OPT = "--devel"

##########################################################################################
#                     CoSA Command Line Arguments and Problem File Options               #
##########################################################################################
#
#     CoSA has an extension of the Python argparse module called CosaArgParser
#       this includes the basic functionality of argparse, but also allows reading
#       configuration files (problem files in CoSA terminology).
#
#     CosaArgParser automatically enforces the following priority order:
#       command line argument > problem option > problem file default > built in default
#
#     where
#       command line argument : a command line argument, this is straightforward
#       problem option        : when the option is set specifically for a particular
#                                 problem in the problem file
#       problem file default  : problem files allow setting default options that apply
#                                 for all the problems in the file
#       built in default      : these are the defaults specified here. If no default is
#                                 provided it will be None
#
#     Additionally, every option is either a GENERAL option or a PROBLEM option.
#       - GENERAL options are set only once per problem file. In general, these are
#         encoding options because the model should only be encoded once per problem file
#       - PROBLEM options are set per-problem within the problem file. These can also be
#         set in the [DEFAULT] section of the problem file
#
#########################################################################################
#     EXAMPLE
#
#     [GENERAL]
#     model_files: example.v[top_mod],reset_procedure.ets
#     abstract_clock: True
#
#     [DEFAULT]
#     bmc_length: 40   # the built in default for bmc_length is 5, but now for the rest of
#                      # this file it will be 40
#     [PROBLEM1]
#     description: "Some description"
#     properties: <formula1>;<formula2>... # <-- note it's best practice to have only one property
#     verification: safety                 # per problem
#
#     [PROBLEM2]
#     description: "Some description"
#     properties: <formula>
#     verification: safety
#     bmc_length: 10                      # <-- bmc_length will be 10 for this problem
#
#     EXAMPLE END
########################################################################################
#
#    Note: if you set an option from the command line when running the problem file
#          it will apply for every problem in the problem file
########################################################################################


########################################################################################
#                               FOR DEVELOPERS                                         #
########################################################################################
#
# Add options here using argparse syntax, this option will automatically be added for
#   problem files as well, using the long option (e.g. the one starting with --)
#   but any dashes will be replaced with underscores
#
# Example: --trace-prefix   is set with trace_prefix in a problem file (and referred to
#          this way within the code)
#
# If you'd like a default, set it with set_default or by passing it as a keyword argument
#   to add_argument
#
# If you do not specify the type, it will be a string.
#
########################################################################################


############################### general set up #########################################
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

PROBLEM_FILE_INFO="""
========================================== Problem File Info ==========================================
CoSA supports problem files (text files describing problem configurations). You can pass a problem file
to CoSA through the --problems option. Please see the "examples" or "tests" directories for examples of
the problem file format. Below is a general description of the option rules.

Every command line option can also be used in a problem file
The option name in a problem file uses the long option (e.g. the one starting with --)
but any dashes will be replaced with underscores

Example:
command line option is --bmc-length
problem file option is bmc_length

Furthermore, options are divided into GENERAL and PROBLEM options (see headers above option sections
in this help message). This is only relevant for setting options in a problem file.
    - GENERAL options are set only once per problem file. In general, these are
        encoding options because the model should only be encoded once per problem file
    - PROBLEM options are set per-problem within the problem file. These can also be
        set in the [DEFAULT] section of the problem file

The following priority order is maintained:
      command line argument > problem option > problem file default > built in default

      where
      command line argument : a command line argument, this is straightforward
      problem option        : when the option is set specifically for a particular
                                problem in the problem file
      problem file default  : problem files allow setting default options that apply
                                for all the problems in the file
      built in default      : these are the defaults specified here. If no default is
                                provided it will be None
"""
extra_info.append(PROBLEM_FILE_INFO)

########################## create option manager and declare options ##########################
cosa_option_manager = CosaArgParser(description=bold_text('CoSA: CoreIR Symbolic Analyzer\n..an SMT-based Symbolic Model Checker for Hardware Design'),
                       formatter_class=RawTextHelpFormatter,
                       epilog="\n".join(extra_info))


# Main inputs

# Options in the general group are options that must stay constant for all problems
# in a problem file

# in our architecture, the input files are compiled into a single transition system which
# is then used to verify mutliple properties (problems)
# thus any option regarding the encoding of said transition system must be a general option

in_options = cosa_option_manager.add_general_group('input options')

av_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                  for x in ModelParsersFactory.get_parsers() if x.is_available()]

ua_input_types = [" - \"%s\": %s"%(x.name, ", ".join(["*.%s"%e for e in x.extensions])) \
                  for x in ModelParsersFactory.get_parsers() if not x.is_available()]

in_options.set_defaults(model_files=None)
in_options.add_argument('-i', '--model_files', metavar='<model files>', type=str, required=False,
                        help='comma separated list of input files.\nSupported types:\n%s%s'%\
                        ("\n".join(av_input_types), "\nNot enabled:\n%s"%("\n".join(ua_input_types)) \
                         if len(ua_input_types) > 0 else ""))

in_options.set_defaults(problems=None)
in_options.add_argument('--problems', metavar='<problems file>', type=str, required=False,
                        help='problems file describing the verifications to be performed.',
                        is_config_file=True)

general_solving_options = cosa_option_manager.add_general_group('solving')

general_solving_options.set_defaults(assume_if_true=False)
general_solving_options.add_argument('--assume-if-true', dest='assume_if_true', action='store_true',
                        help="add true properties as assumptions. (Default is \"%s\")"%False)

general_encoding_options = cosa_option_manager.add_general_group('encoding')

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

general_encoding_options.set_defaults(synchronize=False)
general_encoding_options.add_argument('--synchronize', dest='synchronize', action='store_true',
                                      help='Sychronizes asynchronous behavior, including synchronizing multiple '
                                      'clocks, and abstracts clocks - EXPERTS ONLY. (Default is \"%s\")'%False)

general_encoding_options.set_defaults(symbolic_init=False)
general_encoding_options.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                                      help='removes constraints on the initial state. (Default is \"%s\")'%False)

general_encoding_options.set_defaults(vcd=False)
general_encoding_options.add_argument('--vcd', dest='vcd', action='store_true',
                                      help="generate traces also in vcd format. (Default is \"%s\")"%False)

general_encoding_options.set_defaults(verific=False)
general_encoding_options.add_argument('--verific', action='store_true',
                                      help="Use the verific frontend through Yosys for (System)Verilog "
                                      "input files -- requires a version of Yosys built with Verific "
                                      "bindings. (Default is \"%s\")"%False)

general_encoding_options.set_defaults(zero_init=False)
general_encoding_options.add_argument('--zero-init', dest='zero_init', action='store_true',
                                      help='sets initial state to zero. (Default is \"%s\")'%False)

# General results options
general_results_options = cosa_option_manager.add_general_group('results')

general_results_options.set_defaults(force_expected=False)
general_results_options.add_argument('--force-expected', action='store_true',
                                     help='Force the result to be the provided expected value')

# Problem-specific processing options
problem_processing_options = cosa_option_manager.add_problem_group('problem processing')
problem_processing_options.set_defaults(simplify=False)
problem_processing_options.add_argument('--simplify', action='store_true',
                                        help='simplify formulae with pysmt. (Default is \"%s\")'%False)

# Verification Options

ver_options = cosa_option_manager.add_problem_group('analysis')
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

# Verification parameters

ver_params = cosa_option_manager.add_problem_group('verification parameters')

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

ver_params.set_defaults(equal_to=None)
ver_params.add_argument('--equal-to', required=False, type=str,
                        help='Model to check equivalence with (assumes common interface)')

strategies = [" - \"%s\": %s"%(x[0], x[1]) for x in get_verification_strategies()]
defstrategy = get_verification_strategies()[0][0]
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

# Problem-specific printing parameters
problem_print_params = cosa_option_manager.add_problem_group('trace printing')

problem_print_params.set_defaults(trace_vars_change=False)
problem_print_params.add_argument('--trace-vars-change', dest='trace_vars_change', action='store_true',
                          help="show variable assignments in the counterexamples even when unchanged. (Default is \"%s\")"%False)

problem_print_params.set_defaults(trace_all_vars=False)
problem_print_params.add_argument('--trace-all-vars', dest='trace_all_vars', action='store_true',
                          help="show all variables in the counterexamples. (Default is \"%s\")"%False)

problem_print_params.set_defaults(full_trace=False)
problem_print_params.add_argument('--full-trace', dest='full_trace', action='store_true',
                          help="sets trace-vars-unchanged and trace-all-vars to True. (Default is \"%s\")"%False)

trace_values_base_default = TraceValuesBase.get_all()[0]
problem_print_params.set_defaults(trace_values_base=trace_values_base_default)
problem_print_params.add_argument('--trace-values-base', metavar='trace_values_base', type=str, nargs='?',
                          help="sets the style of Bit-Vector values printing. (Default is \"%s\")"%trace_values_base_default)

problem_print_params.set_defaults(trace_prefix=None)
problem_print_params.add_argument('--trace-prefix', metavar='<trace prefix location>', type=str, required=False,
                   help='write the counterexamples with a specified location prefix.')

# General translation parameters
general_trans_params = cosa_option_manager.add_general_group('translation')

general_trans_params.set_defaults(translate=None)
general_trans_params.add_argument('--translate', metavar='<output file>', type=str, required=False,
                   help='translate input file.')

printers = [" - \"%s\": %s"%(x.get_name(), x.get_desc()) for x in HTSPrintersFactory.get_printers_by_type(HTSPrinterType.TRANSSYS)]
printer_default = HTSPrintersFactory.get_default().get_name()
general_trans_params.set_defaults(printer=printer_default)
general_trans_params.add_argument('--printer', metavar='printer', type=str, nargs='?',
                                  help='select the printer between (Default is \"%s\"):\n%s'%(printer_default, "\n".join(printers)))

# Problem-specific translation parameters

trans_params = cosa_option_manager.add_problem_group('translation')

trans_params.set_defaults(skip_solving=False)
trans_params.add_argument('--skip-solving', dest='skip_solving', action='store_true',
                          help="does not call the solver. (Default is \"%s\")"%False)

# Debugging

deb_params = cosa_option_manager.add_general_group('verbosity')

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
meta_options = cosa_option_manager.add_problem_group('meta')
meta_options.set_defaults(name='ASSERTION')
meta_options.add_argument('--name', type=str, help=argparse.SUPPRESS)

meta_options.set_defaults(description='COMMAND LINE ASSERTION')
meta_options.add_argument('--description', type=str, help=argparse.SUPPRESS)

# Developers
# Options are suppressed from help menu if help called without --devel option
devel_params = cosa_option_manager.add_problem_group('developer')
devel_params.set_defaults(smt2_tracing=None)
devel_params.add_argument('--smt2-tracing', metavar='<smt-lib2 file>', type=str, required=False,
                          help='generates the smtlib2 tracing file for '
                          'each solver call.' if not devel else argparse.SUPPRESS)

devel_params.set_defaults(solver_options=None)
devel_params.add_argument('--solver-options', metavar='[key:value options]', type=str, required=False,
                          help='space delimited key:value pairs '
                          'to set specific SMT solver options (EXPERTS ONLY)' if not devel else argparse.SUPPRESS)

