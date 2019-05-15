#!/usr/bin/env python3
import argparse
from argparse import RawTextHelpFormatter
from collections import defaultdict, namedtuple
import configparser
import itertools
import multiprocessing
from pathlib import Path
from problem import Problems
import sys
from textwrap import TextWrapper
from typing import Dict, Sequence, NamedTuple

from cosa.analyzers.mcsolver import MCConfig
from cosa.utils.generic import auto_convert, bold_text
from cosa.encoders.factory import ModelParsersFactory, GeneratorsFactory, ClockBehaviorsFactory, SyntacticSugarFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.printers.factory import HTSPrintersFactory
from cosa.printers.template import HTSPrinterType, TraceValuesBase

# TODO
# Figure out how to handle verification
# probably want subcommand, but need to fix the extended arg parsers

GENERAL = "GENERAL"
DEFAULT = "DEFAULT"
PROBLEM = "PROBLEM"
BUILTIN = "BUILTIN"

TRACE_PREFIX = "trace"

DEVEL_OPT = "--devel"


class CosaArgGroup(argparse._ArgumentGroup):
    def __init__(self, container, category, group, *args, **kwargs):
        self._category = category
        self._config_files = container._config_files
        self._defaults = container._defaults
        self._add_long_option = container._add_long_option
        argparse._ArgumentGroup.__init__(self, container, '%s.%s'%(category, group), *args, **kwargs)

    def add_argument(self, *args, default=None, dest:str=None, is_config_file:bool=False, **kwargs):
        option_name = self._add_long_option(self._category, args, dest)
        if is_config_file:
            self._config_files.add(option_name)
        if dest is None:
            dest = option_name
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        # always set argparse's default to None so that we can identify
        #  unset arguments
        super().add_argument(*args, default=None, dest=dest, **kwargs)

    def add_mutually_exclusive_group(self, **kwargs):
        group = CosaMutuallyExclusiveGroup(self, self._category, **kwargs)
        self._mutually_exclusive_groups.append(group)
        return group



class CosaMutuallyExclusiveGroup(argparse._MutuallyExclusiveGroup):
    def __init__(self, container, category, **kwargs):
        self._category = category
        self._config_files = container._config_files
        self._defaults = container._config_files
        self._add_long_option = container._add_long_option
        argparse._MutuallyExclusiveGroup.__init__(self, container, **kwargs)
        # placement of this line important -- need to override the None title
        if hasattr(container, 'title'):
            self.title = container.title

    def add_argument(self, *args, default=None, dest:str=None, is_config_file:bool=False, **kwargs):
        option_name = self._add_long_option(self._category, args, dest)
        if is_config_file:
            self._config_files.add(option_name)
        if dest is None:
            dest = option_name
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        super().add_argument(*args, default=None, dest=dest, **kwargs)


class CosaArgParser(argparse.ArgumentParser):
    '''
    The CosaArgParser extends the library class argparse.ArgumentParser to allow
    nested namespaces using a '.' syntax. This is especially useful for unifying
    the command line interface and the problem file syntax.
    '''
    def __init__(self, *args, **kwargs):
        # a set of namespaced options for problem files
        # expecting case-insensitive namespaces 'GENERAL' and 'PROBLEM'
        # problem files also support a DEFAULT section which is not
        #   represented in this structure
        self._config_files = set()
        self._defaults = dict()
        self._problem_options = defaultdict(set)
        self._problem_type = None
        argparse.ArgumentParser.__init__(self, *args, **kwargs)

    def add_argument(self, *args, default=None, dest:str=None, is_config_file:bool=False, **kwargs):
        # adding option with no category group, results in the DEFAULT group
        option_name = self._add_long_option(BUILTIN, args, dest)
        if dest is None:
            dest = option_name
        if is_config_file:
            self._config_files.add(option_name)
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        # always set argparse's default to None so that we can identify
        #   unset arguments
        super().add_argument(*args, default=None, dest=dest, **kwargs)

    def add_argument_group(self, group_str:str, *args, **kwargs)->CosaArgGroup:
        # no specific category results in BUILTIN
        group = CosaArgGroup(self, BUILTIN, group_str, *args, **kwargs)
        self._action_groups.append(group)
        return group

    def add_general_group(self, group_str:str, *args, **kwargs)->CosaArgGroup:
        group = CosaArgGroup(self, GENERAL, group_str, *args, **kwargs)
        self._action_groups.append(group)
        return group

    def add_problem_group(self, group_str:str, *args, **kwargs)->CosaArgGroup:
        group = CosaArgGroup(self, PROBLEM, group_str, *args, **kwargs)
        self._action_groups.append(group)
        return group

    def _add_long_option(self, namespace:str, options:Sequence[str], dest:str)->str:
        '''
        Identify the long version of the option
        '''
        assert len(options) >= 1, "Expecting at least one option"

        if dest is not None:
            option = dest
        else:
            long_options = []
            for o in options:
                if len(o) > 1 and o[:2] == '--':
                    long_options.append(o[2:].replace('-', '_'))
            assert len(long_options) <= 1, "Expecting at most one long option"

            option = long_options[0] if long_options else next(iter(options))

        if namespace and namespace != BUILTIN:
            assert option not in itertools.chain(*self._problem_options.values())
            self._problem_options[namespace].add(option)
        return option

    def set_defaults(self, **kwargs):
        for k, v in kwargs.items():
            self._defaults[k] = v

    def format_help(self):
        formatter = self._get_formatter()

        # usage
        formatter.add_usage(self.usage, self._actions,
                            self._mutually_exclusive_groups)

        # description
        formatter.add_text(self.description)

        # positionals, optionals and user-defined groups
        current_title = ''

        self._action_groups[1:].sort(key=lambda x: x.title)
        for action_group in self._action_groups:
            if '.' in action_group.title:
                title, subtitle = action_group.title.split('.')
                if current_title != title:
                    if current_title:
                        formatter.end_section()
                    formatter.start_section(title.upper())
                    current_title = title
                formatter.start_section(subtitle)
            else:
                formatter.start_section(action_group.title.upper())
            formatter.add_text(action_group.description)
            formatter.add_arguments(action_group._group_actions)
            formatter.end_section()

        # epilog
        formatter.add_text(self.epilog)

        # determine help from format above
        return formatter.format_help()

    def add_mutually_exclusive_group(self, **kwargs)->CosaMutuallyExclusiveGroup:
        group = CosaMutuallyExclusiveGroup(self, **kwargs)
        self._mutually_exclusive_groups.append(group)
        return group

    def get_problem_type(self)->NamedTuple:
        if self._problem_type is None:
            return namedtuple('Problem', ' '.join(self._problem_options[PROBLEM]))
        else:
            assert set(self._problem_type._fields) == set(self._problem_options[PROBLEM].values()), "Problem Type is stale"
            return self._problem_type

    def parse_args(self)->Problems:
        command_line_args = vars(super().parse_args())
        config_files = []
        for config_file in self._config_files:
            if command_line_args[config_file] is not None:
                config_files.append(command_line_args[config_file])
        if config_files:
            assert len(config_files) == 1, "Expecting only a single configuration file"
            problems = self.gen_problems(command_line_args[config_file], command_line_args)
        else:
            # get general options
            general_options = dict()
            for option in self._problem_options[GENERAL]:
                general_options[option] = command_line_args[option]

            problems = Problems(None, general_options, self._defaults)

            # generate a single problem
            problem_type = self.get_problem_type()
            single_problem_options = dict()
            for option in self._problem_options[PROBLEM]:
                if command_line_args[option] is not None:
                    single_problem_options[option] = command_line_args[option]
                else:
                    single_problem_options[option] = self._defaults[option]
            problems.add_problem(problem_type(**single_problem_options))
        return problems

    def parse_config(self, config_file:Path)->configparser.ConfigParser:
        parser = configparser.ConfigParser()
        parser.optionxform=str

        with config_file.open("r") as f:
            parser.read_string(f.read())

        return parser

    def gen_problems(self, config_file:str, command_line_args:Dict[str, str]):
        config_filepath = Path(config_file)
        config_args = self.parse_config(config_filepath)
        general_options = dict(config_args[GENERAL])
        unknown_gen_options = general_options.keys() - self._problem_options[GENERAL]
        if unknown_gen_options:
            raise RuntimeError("Expecting only general options in section"
                               " [GENERAL] but got {}".format(unknown_gen_options))

        problem_defaults = self._defaults.copy()
        default_options = dict(config_args[DEFAULT])
        unknown_default_options = default_options.keys() - self._problem_options[PROBLEM]
        if unknown_default_options:
            raise RuntimeError("Expecting only problem options in section"
                               " [DEFAULT] but got {}".format(unknown_default_options))
        for option, value in default_options.items():
            # override the defaults with problem defaults
            # TODO: use auto_convert here
            # problem_defaults[option] = auto_convert(value)
            problem_defaults[option] = value

        # Generate the problems wrapper and populate it
        problems = Problems(config_filepath, general_options, problem_defaults)

        problem_type = self.get_problem_type()

        # Recall priority order
        # command line > problem option > problem defaults > defaults
        for section in config_args:
            if section == DEFAULT or section == GENERAL:
                continue
            problem_file_options = dict(config_args[section])
            problem_file_options['name'] = section
            for arg in self._problem_options[PROBLEM]:
                if command_line_args[arg] is not None:
                    # overwrite config file with command line arguments
                    problem_file_options[arg] = command_line_args[arg]
                # if the option has still not been set, find a default
                # problem defaults were already given priority
                if arg not in problem_file_options:
                    problem_file_options[arg] = problem_defaults[arg]
            problems.add_problem(problem_type(**problem_file_options))

        return problems

def print_dict(d):
    for k, v in sorted(d.items()):
        print(f'{k}={v}')

def test():
    parser = CosaArgParser()

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

    in_options.set_defaults(model_files=None)
    in_options.add_argument('-i', '--model_files', metavar='<model files>', type=str, required=False,
                            help='comma separated list of input files.\nSupported types:\n%s%s'%\
                            ("\n".join(av_input_types), "\nNot enabled:\n%s"%("\n".join(ua_input_types)) \
                             if len(ua_input_types) > 0 else ""))

    in_options.set_defaults(problems=None)
    in_options.add_argument('--problems', metavar='<problems file>', type=str, required=False,
                            help='problems file describing the verifications to be performed.',
                            is_config_file=True)

    general_encoding_options = parser.add_general_group('encoding')

    general_encoding_options.set_defaults(abstract_clock=False)
    general_encoding_options.add_argument('--abstract-clock', dest='abstract_clock', action='store_true',
                                          help="abstracts the clock behavior. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(add_clock=False)
    general_encoding_options.add_argument('--add-clock', dest='add_clock', action='store_true',
                                          help="adds clock behavior. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(cache_files=False)
    general_encoding_options.add_argument('-c', '--cache-files', dest='cache_files', action='store_true',
                                          help="caches encoded files to speed-up parsing. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(clean_cache=False)
    general_encoding_options.add_argument('--clean-cache', dest='clean_cache', action='store_true',
                                          help="deletes the stored cache. (Default is \"%s\")"%False)

    general_encoding_options.set_defaults(boolean=False)
    general_encoding_options.add_argument('--boolean', dest='boolean', action='store_true',
                                          help='interprets single bits as Booleans instead of 1-bit Bitvector. (Default is \"%s\")'%False)

    general_encoding_options.set_defaults(run_coreir_passes=True)
    general_encoding_options.add_argument('--no-run-coreir-passes', dest='run_coreir_passes', action='store_false',
                                          help='does not run CoreIR passes. (Default is \"%s\")'%True)

    general_encoding_options.set_defaults(model_extension=False)
    general_encoding_options.add_argument('--model-extension', metavar='model_extension', type=str, nargs='?',
                            help='select the model modifier. (Default is \"%s\")'%(False))

    general_encoding_options.set_defaults(opt_circuit=False)
    general_encoding_options.add_argument('--opt-circuit', action='store_true',
                            help='Use Yosys to optimize the circuit -- can remove signals.')

    general_encoding_options.set_defaults(no_arrays=False)
    general_encoding_options.add_argument('--no-arrays', action='store_true',
                            help='For Yosys frontend, blast memories to registers instead of using arrays.\n'
                            'Note: This can fail -- particularly for dualport memories.')

    general_encoding_options.set_defaults(symbolic_init=False)
    general_encoding_options.add_argument('--symbolic-init', dest='symbolic_init', action='store_true',
                                          help='removes constraints on the initial state. (Default is \"%s\")'%False)

    general_encoding_options.set_defaults(zero_init=False)
    general_encoding_options.add_argument('--zero-init', dest='zero_init', action='store_true',
                                          help='sets initial state to zero. (Default is \"%s\")'%False)

    general_encoding_options.set_defaults(vcd=False)
    general_encoding_options.add_argument('--vcd', dest='vcd', action='store_true',
                                          help="generate traces also in vcd format. (Default is \"%s\")"%False)

    general_encoding_options.add_argument('--clock-behaviors', metavar='clock_behaviors', type=str, nargs='?',
                            help='semi column separated list of clock behaviors instantiation.')

    # Verification Options

    ver_options = parser.add_problem_group('analysis')

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

    ver_params = parser.add_problem_group('verification parameters')

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

    ver_params.set_defaults(assume_if_true=False)
    ver_params.add_argument('--assume-if-true', dest='assume_if_true', action='store_true',
                            help="add true properties as assumptions. (Default is \"%s\")"%False)

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

    ver_params.set_defaults(ninc=False)
    ver_params.add_argument('--ninc', dest='ninc', action='store_true',
                            help="disables incrementality. (Default is \"%s\")"%True)

    ver_params.set_defaults(solver_name='msat')
    ver_params.add_argument('--solver-name', metavar='<Solver Name>', type=str, required=False,
                        help="name of SMT solver to be use. (Default is \"%s\")"%'msat')

    # Printing parameters

    print_params = parser.add_problem_group('trace printing')

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

    # Translation parameters

    trans_params = parser.add_problem_group('translation')

    trans_params.set_defaults(translate=None)
    trans_params.add_argument('--translate', metavar='<output file>', type=str, required=False,
                       help='translate input file.')

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

    problems = parser.parse_args()

    for problem in problems._problems:
        print(problem)

if __name__ == "__main__":
    test()
