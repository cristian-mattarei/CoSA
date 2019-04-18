import argparse
from collections import defaultdict, namedtuple
import configparser
import itertools
from pathlib import Path
from typing import Dict, Sequence, NamedTuple

from cosa.problem import ProblemsConfig

GENERAL = "GENERAL"
DEFAULT = "DEFAULT"
PROBLEM = "PROBLEM"
BUILTIN = "BUILTIN"


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

    def parse_args(self)->ProblemsConfig:
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
                if command_line_args[option] is not None:
                    general_options[option] = command_line_args[option]
                else:
                    general_options[option] = self._defaults[option]

            problems = ProblemsConfig(None, general_options, self._defaults)

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
        for option, value in general_options.items():
            # replace empty arguments with default value
            if value is None:
                general_options[option] = self._defaults[option]
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
        problems = ProblemsConfig(config_filepath, general_options, problem_defaults)

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
