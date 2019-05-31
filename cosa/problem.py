# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from collections import namedtuple
import configparser
import copy
from itertools import count
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Set, Sequence, Union

# for type hints
from pysmt.fnode import FNode

from cosa.encoders.formulae import StringParser
from cosa.representation import HTS
from cosa.utils.generic import auto_convert, simple_struct
from cosa.utils.logger import Logger


## For unique problem ids
counter = count()
get_id = lambda : next(counter)

DEFAULT = "DEFAULT"
GENERAL = "GENERAL"
VERIFICATION = "verification"
LIVENESS = "liveness"
EVENTUALLY = "eventually"
SAFETY = "safety"
PARAMETRIC = "parametric"
LTL = "ltl"
EQUIVALENCE = "equivalence"
SIMULATION = "simulation"
DETERMINISTIC = "deterministic"
FORMULA = "formula"
MODEL_FILE = "model_files"

MODEL_SP = ";"
FILE_SP  = ","
NL       = '\n'

class VerificationStatus(object):
    UNC = "UNCHECKED"
    UNK = "UNKNOWN"
    TRUE = "TRUE"
    FALSE = "FALSE"

    @staticmethod
    def convert(status):
        if type(status) == bool:
            return VerificationStatus.TRUE if status else VerificationStatus.FALSE

        if status.upper() in [VerificationStatus.TRUE,\
                              VerificationStatus.FALSE,\
                              VerificationStatus.UNK,\
                              VerificationStatus.UNC]:
            return status.upper()

        Logger.error("Invalid Verification Status \"%s\""%status)

    @staticmethod
    def compare(expected, status):
        if (expected == VerificationStatus.UNK) and (status == VerificationStatus.TRUE):
            return True
        return expected == status

class VerificationType(object):
    SAFETY = SAFETY
    LIVENESS = LIVENESS
    EVENTUALLY = EVENTUALLY
    EQUIVALENCE = EQUIVALENCE
    DETERMINISTIC = DETERMINISTIC
    SIMULATION = SIMULATION
    LTL = LTL
    PARAMETRIC = PARAMETRIC


# This class should not be instantiated directly
# it is instantiated and populated with the correct options
# by cosa.config.CosaArgParser
class ProblemsManager:
    '''
    '''
    def __init__(self, relative_path:Path, general_config:Dict[str, Any], defaults:Dict[str, Any]):
        # after calling freeze, all existing problems will become immutable
        # note, can still add new (immutable) problems, but can't modify existing ones
        self._frozen                = False
        self._relative_path         = relative_path
        # sorting keeps everything deterministic
        general_config_options      = sorted(list(general_config.keys()))
        self._general_config        = simple_struct('general_config',
                                                    general_config_options)(**general_config)
        self._defaults              = defaults
        self._problems              = []
        # solving status
        self._problems_status       = dict()
        # counter example traces
        self._problems_traces       = dict()
        # runtime
        self._problems_time         = dict()
        # region for parametric model checking
        self._problems_region       = dict()

        # The main Hierarchical Transition System that all problems are run on
        self._hts                   = None
        # Per-problem second systems for equivalence checking (of verification=equivalence)
        self._problems_second_model = dict()

        # sorting keeps everything deterministic
        options = sorted(list(defaults.keys()))
        options.append('idx') # unique id for internal use
        self.__problem_type         = namedtuple('Problem', options)
        self.__mutable_problem_type = simple_struct('MutableProblem', options)

    def set_defaults(self, problem:NamedTuple):
        '''
        Set the problem default values based on a given problem. This is used when
        solving embedded assertions. Problems might be added in analyzer/dispatcher.py,
        but we should maintain the options that were set from the command line.
        '''
        problem_dict = problem._asdict()
        unknown_problem_dict = problem_dict.keys() - self.__problem_type._fields
        if unknown_problem_dict:
            raise RuntimeError("Expecting only known problem "
                               "options but got {}".format(unknown_problem_dict))

        for k, v in problem_dict.items():
            if k != 'idx':
                # don't re-use the index
                self._defaults[k] = v

    def add_problem(self, frozen=True, **kwargs):
        '''
        Creates a problem with the given kwargs as fields,
        anything not supplied is given the default value
        as determined by the defaults given to CosaArgParser in shell.py

        if frozen, then problem is an immutable namedtuple
        otherwise, creates a mutable simple_struct (a CoSA data structure)
        --> this is for post-processing in CosaArgParser
            some options implicitly set other options and this must be managed
            once that is all done, the problems should be frozen, by calling
            .freeze() on the ProblemsManager object (done in config.py)
        '''

        if self._frozen:
            # problems should not be mutable
            # the only case is BEFORE implicitly setting options in config.py
            assert frozen, "Can't add a mutable problem after the manager has been frozen"

        unknown_kwargs = kwargs.keys() - self.__problem_type._fields
        if unknown_kwargs:
            raise RuntimeError("Expecting only known problem "
                               "options but got {}".format(unknown_kwargs))

        # start with the defaults, but don't overwrite the defaults
        problem_options = self._defaults.copy()
        for option, value in kwargs.items():
            problem_options[option] = value

        # if there were multiple properties, split them into separate problems
        # doesn't apply for None (obviously) or FNode (which is already a compiled property)
        #    Note: FNodes are only used for embedded assertions (included in the model file)
        #          because those are already processed by the encoder
        if problem_options['properties'] is not None and \
           type(problem_options['properties']) is not FNode:
            problems = self._split_problem(problem_options)
            for pbm in problems:
                self._problems.append(pbm)
                self._problems_status[pbm.idx] = VerificationStatus.UNC
        else:
            problem = self.__problem_type(idx=get_id(), **problem_options)
            self._problems.append(problem)
            self._problems_status[problem.idx] = VerificationStatus.UNC

    def _split_problem(self, problem_options:Dict[str, Any]):
        '''
        Split a problem with multiple properties into multiple problems
        Generate a new name for each
        '''

        problems = []
        properties = None
        if isinstance(problem_options['properties'], str):
            try:
                potential_filepath = self.relative_path / problem_options['properties']
                properties = []
                with potential_filepath.open() as f:
                    for line in f.read().split(NL):
                        line = line.strip()
                        if line:
                            properties.append(line)
            except OSError:
                properties = [p.strip() for p in problem_options['properties'].strip().split(MODEL_SP)]
                if not properties[-1]:
                    properties = properties[:-1]
        elif isinstance(problem_options['properties'], Sequence):
            properties = problem_options['properties']
        else:
            assert False, "should be unreachable"

        assert properties is not None
        name = problem_options['name']
        names = ['{}_{}'.format(name, i) for i in range(len(properties))]

        # Remove old properties and name
        del problem_options['properties']
        del problem_options['name']

        for n, prop in zip(names, properties):
            # create new problems with new name and properties field
            # and the rest of the fields identical
            problems.append(self.__mutable_problem_type(name=n, properties=prop,
                                                        idx=get_id(), **problem_options))

        return problems

    def freeze(self):
        assert not self._frozen, "Already frozen -- not expecting to have freeze called twice"
        self._frozen = True
        # freeze the general_config
        self._general_config = namedtuple('general_config',
                                          self._general_config.keys())(**self._general_config)
        # freeze all the problems as (immutable) namedtuples
        for i, pbm in enumerate(self.problems):
            try:
                self._problems[i] = self.__problem_type(**pbm)
            except:
                pass

    def set_problem_status(self, problem:NamedTuple, status:VerificationStatus):
        assert self._problems_status[problem.idx] == VerificationStatus.UNC, \
            "Not expecting to reset problem status"
        self._problems_status[problem.idx] = status

    def get_problem_status(self, problem:NamedTuple)->VerificationStatus:
        return self._problems_status[problem.idx]

    def set_problem_traces(self, problem:NamedTuple, traces:Union[List, object]):
        self._problems_traces[problem.idx] = traces

    def get_problem_traces(self, problem:NamedTuple):
        return self._problems_traces[problem.idx]

    def has_problem_trace(self, problem:NamedTuple):
        return problem.idx in self._problems_traces

    def set_problem_time(self, problem:NamedTuple, time:float):
        self._problems_time[problem.idx] = time

    def get_problem_time(self, problem:NamedTuple)->float:
        return self._problems_time[problem.idx]

    def set_problem_region(self, problem:NamedTuple, region:Optional[List[FNode]])->None:
        self._problems_region[problem.idx] = region

    def get_problem_region(self, problem:NamedTuple)->Optional[List[FNode]]:
        return self._problems_region[problem.idx]

    def add_second_model(self, problem:NamedTuple, hts:HTS):
        self._problems_second_model[problem.idx] = hts

    def get_second_model(self, problem:NamedTuple):
        return self._problems_second_model[problem.idx]

    @property
    def problems(self)->List[NamedTuple]:
        return self._problems

    @property
    def general_config(self)->NamedTuple:
        return self._general_config

    @property
    def hts(self):
        return self._hts

    @hts.setter
    def hts(self, hts:HTS):
        self._hts = hts

    @property
    def hts2(self):
        return self.hts2

    @hts2.setter
    def hts2(self, hts:HTS):
        self._hts2 = hts

    @property
    def relative_path(self):
        return self._relative_path


class Trace(object):
    name = ""
    description = ""
    extension = None
    strtrace = None
    model = None
    length = None
    infinite = False
    human_readable = False
    prop_vars = None

    def __init__(self, strtrace=None, length=None):
        self.strtrace = strtrace
        self.length = length

    def __repr__(self):
        return str(self.strtrace)

    def __str__(self):
        return str(self.strtrace)
