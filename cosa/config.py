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
from collections import defaultdict, namedtuple
import configparser
import itertools
from pathlib import Path
from typing import Callable, Dict, Sequence, NamedTuple

from cosa.analyzers.mcsolver import VerificationStrategy
from cosa.problem import ProblemsManager, VerificationType

GENERAL = "GENERAL"
DEFAULT = "DEFAULT"
PROBLEM = "PROBLEM"
BUILTIN = "BUILTIN"


class CosaArgGroup(argparse._ArgumentGroup):
    def __init__(self, container, category, group, *args, **kwargs):
        self._category = category
        self._config_files = container._config_files
        self._defaults = container._defaults
        self._types = container._types
        self._add_long_option = container._add_long_option
        argparse._ArgumentGroup.__init__(self, container, '%s.%s'%(category, group), *args, **kwargs)

    def add_argument(self, *args, default=None, action=None,
                     dest:str=None, is_config_file:bool=False,
                     type:Callable=str, **kwargs):
        option_name = self._add_long_option(self._category, args, dest)
        if is_config_file:
            self._config_files.add(option_name)
        if dest is None:
            dest = option_name
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        if option_name not in self._types:
            if action == 'store_true':
                self._types[option_name] = bool
            else:
                self._types[option_name] = type
        # always set argparse's default to None so that we can identify
        #  unset arguments
        super().add_argument(*args, default=None, dest=dest, action=action, **kwargs)

    def add_mutually_exclusive_group(self, **kwargs):
        group = CosaMutuallyExclusiveGroup(self, self._category, **kwargs)
        self._mutually_exclusive_groups.append(group)
        return group



class CosaMutuallyExclusiveGroup(argparse._MutuallyExclusiveGroup):
    def __init__(self, container, category, **kwargs):
        self._category = category
        self._config_files = container._config_files
        self._defaults = container._config_files
        self._types = container._types
        self._add_long_option = container._add_long_option
        argparse._MutuallyExclusiveGroup.__init__(self, container, **kwargs)
        # placement of this line important -- need to override the None title
        if hasattr(container, 'title'):
            self.title = container.title

    def add_argument(self, *args, default=None, action=None,
                     dest:str=None, is_config_file:bool=False,
                     type:Callable=str, **kwargs):
        option_name = self._add_long_option(self._category, args, dest)
        if is_config_file:
            self._config_files.add(option_name)
        if dest is None:
            dest = option_name
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        if option_name not in self._types:
            if action == 'store_true':
                self._types[option_name] = bool
            else:
                self._types[option_name] = type
        super().add_argument(*args, default=None, dest=dest, action=action, **kwargs)


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
        self._types = dict()
        self._problem_options = defaultdict(set)
        self._problem_type = None
        argparse.ArgumentParser.__init__(self, *args, **kwargs)

    def add_argument(self, *args, default=None, action=None,
                     dest:str=None, is_config_file:bool=False,
                     type:Callable=str, **kwargs):
        # adding option with no category group, results in the DEFAULT group
        option_name = self._add_long_option(BUILTIN, args, dest)
        if dest is None:
            dest = option_name
        if is_config_file:
            self._config_files.add(option_name)
        # save the default (if not already set)
        if option_name not in self._defaults:
            self._defaults[option_name] = default
        if option_name not in self._types:
            if action == 'store_true':
                self._types[option_name] = bool
            else:
                self._types[option_name] = type
        # always set argparse's default to None so that we can identify
        #   unset arguments
        super().add_argument(*args, default=None, dest=dest, action=action, **kwargs)

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

        action_groups = self._action_groups[1:]
        action_groups.sort(key=lambda x: x.title)

        for action_group in itertools.chain([self._action_groups[0]], action_groups):
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

    def get_default_problem_manager(self, **kwargs)->ProblemsManager:
        '''
        Returns the problem manager with default general options, which can be overriden
        with the keyword arguments.

        See the options.py file for the possible keywords
          where dashes in long option names are replaced by underscores
          (and leading dashes are removed)
          e.g. --trace-prefix is trace_prefix
        '''

        unknown_gen_options = kwargs.keys() - self._problem_options[GENERAL]
        if unknown_gen_options:
            raise RuntimeError("Expecting only general options in section"
                               "but got {}.\nGeneral options include:\n"
                               "{}".format(unknown_gen_options,
                                           '\n\t'.join(self._problem_options[GENERAL])))

        general_options = dict()
        for option in self._problem_options[GENERAL]:
            if option in kwargs:
                general_options[option] = kwargs[option]
            else:
                general_options[option] = self._defaults[option]

        problem_defaults = {o:self._defaults[o] for o in self._problem_options[PROBLEM]}

        return ProblemsManager(Path("./"), general_options, problem_defaults)

    def parse_args(self)->ProblemsManager:
        command_line_args = vars(super().parse_args())
        config_files = []
        for config_file in self._config_files:
            if command_line_args[config_file] is not None:
                config_files.append(command_line_args[config_file])
        if config_files:
            assert len(config_files) == 1, "Expecting only a single configuration file"
            problems_manager = self.read_problem_file(command_line_args[config_file], _command_line_args=command_line_args)
        else:
            # get general options
            general_options = dict()
            for option in self._problem_options[GENERAL]:
                if command_line_args[option] is not None:
                    general_options[option] = command_line_args[option]
                else:
                    general_options[option] = self._defaults[option]

            # convert options to expected type
            for k, v in general_options.items():
                if v is not None:
                    assert k in self._types, "Expecting to have (at least default) type info for every option"
                    try:
                        general_options[k] = self._types[k](v)
                    except ValueError as e:
                        raise ValueError("Cannot convert '{}' to expected type {}".format(v, self._types[k]))

            # create default options for only problem fields
            problem_defaults = {o:self._defaults[o] for o in self._problem_options[PROBLEM]}
            problems_manager = ProblemsManager(Path("./"), general_options, problem_defaults)

            # generate a single problem
            single_problem_options = dict()
            for option in self._problem_options[PROBLEM]:
                if command_line_args[option] is not None:
                    single_problem_options[option] = command_line_args[option]
                else:
                    single_problem_options[option] = self._defaults[option]

            for k, v in single_problem_options.items():
                if v is not None:
                    assert k in self._types, "Expecting to have (at least default) type info for every option"
                    try:
                        single_problem_options[k] = self._types[k](v)
                    except ValueError as e:
                        raise ValueError("Cannot convert '{}' to expected type {}".format(v, self._types[k]))

            # calling with frozen=False keeps the problem mutable for now (might not to override options)
            problems_manager.add_problem(**single_problem_options, frozen=False)

        # run any manual option handling
        # modifies the problems_manager in-place
        self._option_handling(problems_manager)
        # freeze the problems
        # now all existing problems are (immutable) namedtuples
        # note, you can still add new problems, but they must be frozen (e.g. immutable)
        problems_manager.freeze()

        return problems_manager

    def parse_config(self, config_file:Path)->configparser.ConfigParser:
        parser = configparser.ConfigParser()
        parser.optionxform=str

        with config_file.open("r") as f:
            parser.read_string(f.read())

        return parser

    def read_problem_file(self, config_file:str,
                          _command_line_args:Dict[str, str]=dict(),
                          **kwargs)->ProblemsManager:
        '''
        Reads a problem file and then overrides defaults with command line options
        if any were provided.

        Users should not pass _command_line_args directly, that is for internal use only.
        Instead, pass options through keyword arguments.
        '''
        config_filepath = Path(config_file)
        config_args = self.parse_config(config_filepath)
        general_options = dict(config_args[GENERAL])

        # populate command line arguments with keyword arguments if provided
        if kwargs:
            # check that all options are valid
            unknown_kwargs = (kwargs.keys() - self._problem_options[GENERAL]) - \
                              self._problem_options[PROBLEM]

            if unknown_kwargs:
                raise RuntimeError("Expected only valid CoSA options as "
                                   "keyword arguments but got {}.\nPlease select "
                                   "from:\n\t{}\n\nValid options can be also be viewed "
                                   "with --help".format(unknown_kwargs,
                                                        '\n\t'.join(
                                                            sorted(itertools.chain(
                                                            self._problem_options[GENERAL],
                                                            self._problem_options[PROBLEM])))))

            # command line arguments should contain everything or nothing
            # populate with none if we need to override with keyword arguments
            if not _command_line_args:
                for option in itertools.chain(self._problem_options[GENERAL],
                                              self._problem_options[PROBLEM]):
                    _command_line_args[option] = None
            for option, v in kwargs.items():
                _command_line_args[option] = v

        # remove default options
        # -- configparser automatically populates defaults
        #    in every section, which we don't want
        for option in config_args[DEFAULT]:
            general_options.pop(option, None)

        unknown_gen_options = general_options.keys() - self._problem_options[GENERAL]
        if unknown_gen_options:
            raise RuntimeError("Expecting only general options in section"
                               " [GENERAL] but got {} in {}".format(unknown_gen_options, config_file))

        # populate with general defaults
        # as an optimization, don't even check _command_line_args if it's empty
        if _command_line_args:
            for option in self._problem_options[GENERAL]:
                if option not in general_options or general_options[option] is None:
                    if _command_line_args[option] is not None:
                        general_options[option] = _command_line_args[option]
                    else:
                        general_options[option] = self._defaults[option]
        else:
            for option in self._problem_options[GENERAL]:
                if option not in general_options or general_options[option] is None:
                    general_options[option] = self._defaults[option]

        problem_defaults = {o:self._defaults[o] for o in self._problem_options[PROBLEM]}
        default_options = dict(config_args[DEFAULT])
        unknown_default_options = default_options.keys() - self._problem_options[PROBLEM]
        if unknown_default_options:
            raise RuntimeError("Expecting only problem options in section"
                               " [DEFAULT] but got {} in {}".format(unknown_default_options, config_file))
        for option, value in default_options.items():
            # override the defaults with problem defaults
            problem_defaults[option] = value

        # convert options to expected type
        for k, v in general_options.items():
            if v is not None:
                assert k in self._types, "Expecting to have (at least default) type info for every option"
                try:
                    # handle the 'False' case, note that bool('False') evaluates to True
                    if self._types[k] == bool and isinstance(v, str):
                        if v == 'True':
                            general_options[k] = True
                        elif v == 'False':
                            general_options[k] = False
                        else:
                            raise RuntimeError("Expecting True or False as an option for {} but got {}".format(k, v))
                    else:
                        general_options[k] = self._types[k](v)
                except ValueError as e:
                    raise ValueError("Cannot convert '{}' to expected type {}".format(v, self._types[k]))

        # Generate the problems_manager and populate it
        problems_manager = ProblemsManager(config_filepath.parent, general_options, problem_defaults)

        # Recall priority order
        # command line > problem option > problem defaults > defaults
        for section in config_args:
            if section == DEFAULT or section == GENERAL:
                continue
            problem_file_options = dict(config_args[section])
            unknown_problem_file_options = problem_file_options.keys() - self._problem_options[PROBLEM]
            if unknown_problem_file_options:
                raise RuntimeError("Expecting only problem options "
                                   "in problem section but got {} in {}".format(unknown_problem_file_options, config_file))


            # The [HEADER] style sections become problem names
            problem_file_options['name'] = section

            if _command_line_args:
                for arg in self._problem_options[PROBLEM]:
                    if _command_line_args[arg] is not None:
                        # overwrite config file with command line arguments
                        problem_file_options[arg] = _command_line_args[arg]
                    # if the option has still not been set, find a default
                    # problem defaults were already given priority
                    if arg not in problem_file_options:
                        problem_file_options[arg] = problem_defaults[arg]
            else:
                # set defaults if not explicitly set in this particular problem
                for arg in self._problem_options[PROBLEM]:
                    if arg not in problem_file_options:
                        problem_file_options[arg] = problem_defaults[arg]

            for k, v in problem_file_options.items():
                if v is not None:
                    assert k in self._types, "Expecting to have (at least default) type info for every option"
                    try:
                        # handle the 'False' case, note that bool('False') evaluates to True
                        if self._types[k] == bool and isinstance(v, str):
                            if v == 'True':
                                problem_file_options[k] = True
                            elif v == 'False':
                                problem_file_options[k] = False
                            else:
                                raise RuntimeError("Expecting True or False as an option for {} but got {}".format(k, v))
                        else:
                            problem_file_options[k] = self._types[k](v)
                    except ValueError as e:
                        raise ValueError("Cannot convert '{}' to expected type {}".format(v, self._types[k]))

            try:
                # using frozen=False keeps the problems mutable for now
                problems_manager.add_problem(**problem_file_options, frozen=False)
            except TypeError as e:
                if len(e.args) > 0:
                    message = e.args[0]
                if "unexpected keyword argument" in message:
                    unknown_option = message[message.find("argument ")+9:]
                    raise RuntimeError("Unknown option in problem file: {}".format(unknown_option))
                else:
                    raise e
        return problems_manager

    def _option_handling(self, problems_manager:ProblemsManager)->None:
        '''
        Do any necessary manual option handling.
        E.g. if some options implicitly set other options, this needs to happen here

        This method should be (carefully) modified whenever a new option is added that is not
        completely independent of other options (e.g. might affect how other options need to be set).
        '''

        general_config = problems_manager.general_config

        # handle case where no properties are given
        # i.e. expecting embedded assertions in the model file
        # command_line is True when no problem file was used (e.g. not argument for --problems)
        command_line = general_config.problems is None
        if command_line and len(problems_manager.problems) == 1:
            pbm = problems_manager.problems[0]
            if pbm.properties is None and \
               pbm.verification not in {VerificationType.EQUIVALENCE, VerificationType.SIMULATION}:
                # use the provided (command line) options as defaults
                problems_manager.set_defaults(pbm)
                # remove the problem
                problems_manager._problems = []
                problems_manager._problems_status = dict()

        ################## synchronizing clock automatically abstracts ###################
        if general_config.synchronize:
            general_config.abstract_clock = True

        # iterate through problems and fix options
        for problem in problems_manager.problems:

            ########################### parametric model checking ############################
            # parametric model checking uses strategy BWD
            # need to set the strategy for interpreting traces correctly
            if problem.verification == VerificationType.PARAMETRIC:
                problem.strategy = VerificationStrategy.BWD

        return problems_manager
