# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import copy
import os
import pickle

from collections import Sequence
from pathlib import Path
from typing import List, NamedTuple, Optional, Union

from pysmt.fnode import FNode
from pysmt.shortcuts import Symbol, Implies, get_free_variables, BV, TRUE, simplify, And, EqualsOrIff, Array

from cosa.utils.logger import Logger
from cosa.analyzers.mcsolver import CONST_ARRAYS_SUPPORT
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_parametric import BMCParametric
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationType, VerificationStatus, Trace
from cosa.encoders.miter import Miter
from cosa.encoders.formulae import StringParser
from cosa.representation import HTS, TS, L_ABV
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.ltl import LTLParser
from cosa.encoders.factory import ModelParsersFactory, ClockBehaviorsFactory, GeneratorsFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.modifiers.coi import ConeOfInfluence
from cosa.encoders.template import ModelInformation
from cosa.encoders.parametric_behavior import ParametricBehavior
from cosa.printers.trace import TextTracePrinter, VCDTracePrinter
from cosa.modifiers.model_extension import ModelExtension
from cosa.encoders.symbolic_transition_system import SymbolicSimpleTSParser
from cosa.printers.factory import HTSPrintersFactory
from cosa.printers.hts import STSHTSPrinter
from cosa.problem import ProblemsManager, MODEL_SP, FILE_SP


FLAG_SR = "["
FLAG_ST = "]"
FLAG_SP = "+"

COSACACHEDIR = ".CoSA/cache"

class ProblemSolver(object):
    parser = None
    sparser = None
    lparser = None
    model_info = None
    coi = None

    def __init__(self):
        self.sparser = None
        self.lparser = None
        self.coi = None
        self.model_info = ModelInformation()

        GeneratorsFactory.init_generators()
        ClockBehaviorsFactory.init_clockbehaviors()


    def __process_trace(self, hts, trace, config, problem):
        prevass = []

        full_trace = problem.full_trace
        trace_vars_change = problem.trace_vars_change
        trace_all_vars = problem.trace_all_vars
        trace_values_base = problem.trace_values_base

        diff_only = not trace_vars_change
        all_vars = trace_all_vars

        txttrace_synth_clock = False

        if full_trace:
            diff_only = False
            all_vars = True

        traces = []
        abstract_clock_list = []

        if txttrace_synth_clock:
            abstract_clock_list=self.model_info.abstract_clock_list

        # Human Readable Format
        hr_printer = TextTracePrinter()
        hr_printer.prop_vars = trace.prop_vars
        hr_printer.diff_only = diff_only
        hr_printer.all_vars = all_vars
        hr_printer.values_base = trace_values_base
        hr_trace = hr_printer.print_trace(hts=hts, \
                                          model=trace.model, \
                                          length=trace.length, \
                                          map_function=self.parser.remap_an2or, \
                                          find_loop=trace.infinite, \
                                          abstract_clock_list=abstract_clock_list)
        traceH = Trace(hr_trace, trace.length)
        traceH.extension = hr_printer.get_file_ext()
        traceH.human_readable = hr_trace.human_readable
        traces.append(traceH)

        # VCD format
        vcd_trace = None
        if config.vcd:
            vcd_printer = VCDTracePrinter()
            vcd_printer.all_vars = all_vars
            vcd_trace = vcd_printer.print_trace(hts=hts, \
                                                model=trace.model, \
                                                length=trace.length, \
                                                map_function=self.parser.remap_an2or, \
                                                abstract_clock_list=self.model_info.abstract_clock_list)
            traceV = Trace(vcd_trace, trace.length)
            traceV.extension = vcd_printer.get_file_ext()
            traceV.human_readable = vcd_trace.human_readable
            traces.append(traceV)

        return traces

    def __solve_problem(self,
                        hts:HTS,
                        prop:Optional[FNode],
                        lemmas:Optional[List[FNode]],
                        assumptions:Optional[List[FNode]],
                        problem:NamedTuple)->str:

        trace = None
        traces = None
        region = None # only used for parametric model checking

        accepted_ver = False

        assert hts.assumptions is None, "There should not be any left-over assumptions from previous problems"
        for assump in assumptions:
            hts.add_assumption(assump)
        for lemma in lemmas:
            hts.add_lemma(lemma)

        bmc_safety = BMCSafety(hts, problem)
        bmc_parametric = BMCParametric(hts, problem)
        bmc_ltl = BMCLTL(hts, problem)
        res = VerificationStatus.UNC

        bmc_length = problem.bmc_length
        bmc_length_min = problem.bmc_length_min

        if problem.verification == VerificationType.SAFETY:
            accepted_ver = True
            Logger.log("Property: %s"%(prop.serialize(threshold=100)), 2)
            res, trace, _ = bmc_safety.safety(prop, bmc_length, bmc_length_min, problem.processes)

        if problem.verification == VerificationType.LTL:
            accepted_ver = True
            res, trace, _ = bmc_ltl.ltl(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.SIMULATION:
            accepted_ver = True
            res, trace = bmc_safety.simulate(prop, bmc_length)

        if problem.verification == VerificationType.PARAMETRIC:
            accepted_ver = True
            Logger.log("Property: %s"%(prop.serialize(threshold=100)), 2)
            res, traces, region = bmc_parametric.parametric_safety(prop, bmc_length, bmc_length_min, ModelExtension.get_parameters(hts), at_most=problem.cardinality)

        if problem.verification == VerificationType.EQUIVALENCE:
            accepted_ver = True
            bmcseq = BMCSafety(hts, problem)
            res, trace, t = bmcseq.safety(prop, bmc_length, bmc_length_min)

        if not accepted_ver:
            Logger.error("Invalid verification type")

        Logger.log("\n*** Problem \"%s\" is %s ***"%(problem.name, res), 1)
        return res, trace, traces, region

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)

        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)

    def md5(self, fname:Path):
        import hashlib
        hash_md5 = hashlib.md5()
        with fname.open('rb') as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_md5.update(chunk)
        return hash_md5.hexdigest()

    def _is_cached(self, cachedir, filename, clean):
        hts_file = "%s/%s.ssts"%(cachedir, filename)
        mi_file = "%s/%s.mi"%(cachedir, filename)
        inv_file = "%s/%s.inv"%(cachedir, filename)
        ltl_file = "%s/%s.ltl"%(cachedir, filename)

        if clean:
            if os.path.isfile(hts_file):
                os.remove(hts_file)
            if os.path.isfile(mi_file):
                os.remove(mi_file)
            if os.path.isfile(inv_file):
                os.remove(inv_file)
            if os.path.isfile(ltl_file):
                os.remove(ltl_file)

        return os.path.isfile(hts_file) and \
            os.path.isfile(mi_file) and \
            os.path.isfile(inv_file) and \
            os.path.isfile(ltl_file)

    def _to_cache(self, cachedir, filename, hts, inv, ltl, model_info):
        if not os.path.isdir(cachedir):
            os.makedirs(cachedir)

        hts_file = "%s/%s.ssts"%(cachedir, filename)
        mi_file = "%s/%s.mi"%(cachedir, filename)
        inv_file = "%s/%s.inv"%(cachedir, filename)
        ltl_file = "%s/%s.ltl"%(cachedir, filename)

        printer = HTSPrintersFactory.printer_by_name(STSHTSPrinter().get_name())
        with open(hts_file, "w") as f:
            f.write(printer.print_hts(hts, properties=[], ftrans=True))

        with open(mi_file, 'wb') as f:
            pickle.dump(model_info, f)

        with open(inv_file, 'wb') as f:
            pickle.dump(inv, f)

        with open(ltl_file, 'wb') as f:
            pickle.dump(ltl, f)

    def _from_cache(self, cachedir, filename, config, flags):
        hts_file = "%s/%s.ssts"%(cachedir, filename)
        mi_file = "%s/%s.mi"%(cachedir, filename)
        inv_file = "%s/%s.inv"%(cachedir, filename)
        ltl_file = "%s/%s.ltl"%(cachedir, filename)

        parser = SymbolicSimpleTSParser()

        hts = parser.parse_file(hts_file, config, flags)[0]

        with open(mi_file, 'rb') as f:
            model_info = pickle.load(f)
            if model_info is not None:
                # Symbols have to be re-defined to match the current object addresses
                model_info.abstract_clock_list = [(Symbol(x[0].symbol_name(), x[0].symbol_type()), x[1]) for x in model_info.abstract_clock_list]
                model_info.clock_list = [Symbol(x.symbol_name(), x.symbol_type()) for x in model_info.clock_list]

        with open(inv_file, 'rb') as f:
            inv = pickle.load(f)

        with open(ltl_file, 'rb') as f:
            ltl = pickle.load(f)

        return (hts, inv, ltl, model_info)

    def parse_model(self, \
                    model_files,
                    relative_path, \
                    general_config, \
                    name=None, \
                    modifier=None):

        hts = HTS(name if name is not None else "System")
        invar_props = []
        ltl_props = []

        models = model_files.split(FILE_SP)
        cache_files = general_config.cache_files
        clean_cache = general_config.clean_cache

        for strfile in models:
            (strfile, flags) = self.get_file_flags(strfile)
            if len(strfile) > 1 and strfile[:2] == '~/':
                filepath = Path.home() / Path(strfile[2:])
            else:
                filepath = Path(strfile)
            if filepath.parts[0] != "/":
                filepath = relative_path / filepath
            filetype = filepath.suffix[1:]
            parser = None

            for av_parser in ModelParsersFactory.get_parsers():
                assert av_parser.name is not None
                if filetype in av_parser.get_extensions():
                    parser = av_parser
                    if not self.parser:
                        self.parser = av_parser

            if parser is not None:
                if not filepath.is_file():
                    Logger.error("File \"%s\" does not exist"%filepath)

                if cache_files:
                    md5 = self.md5(filepath)
                    cf = "-".join(["1" if general_config.abstract_clock else "0", \
                                   "1" if general_config.add_clock else "0", \
                                   "1" if general_config.boolean else "0"])
                    cachefile = "%s-%s"%(md5, cf)
                    cachedir = filepath.parent / COSACACHEDIR

                if cache_files and self._is_cached(cachedir, cachefile, clean_cache):
                    Logger.msg("Loading from cache file \"%s\"... "%(filepath), 0)
                    (hts_a, inv_a, ltl_a, model_info) = self._from_cache(cachedir, cachefile, general_config, flags)
                else:
                    Logger.msg("Parsing file \"%s\"... "%(filepath), 0)
                    (hts_a, inv_a, ltl_a) = parser.parse_file(filepath, general_config, flags)

                    model_info = parser.get_model_info()

                    if modifier is not None:
                        modifier(hts_a)

                    if cache_files and not clean_cache:
                        self._to_cache(cachedir, cachefile, hts_a, inv_a, ltl_a, model_info)

                self.model_info.combine(model_info)
                hts.combine(hts_a)

                invar_props += inv_a
                ltl_props += ltl_a

                Logger.log("DONE", 0)
                continue

            Logger.error("Filetype \"%s\" unsupported or parser is not available"%filetype)

        if Logger.level(1):
            print(hts.print_statistics(name, Logger.level(2)))

        return (hts, invar_props, ltl_props)

    def solve_problems(self, problems_config:ProblemsManager)->None:

        general_config  = problems_config.general_config
        model_extension = general_config.model_extension
        assume_if_true  = general_config.assume_if_true

        self.sparser = StringParser(general_config)
        self.lparser = LTLParser()

        self.coi = ConeOfInfluence()

        modifier = None
        if general_config.model_extension is not None:
            modifier = lambda hts: ModelExtension.extend(hts,
                        ModelModifiersFactory.modifier_by_name(general_config.model_extension))

        hierarchical_transition_systems = []

        # generate main system system
        hts, invar_props, ltl_props = self.parse_model(general_config.model_files,
                                                       problems_config.relative_path,
                                                       general_config,
                                                       "System 1",
                                                       modifier)

        hierarchical_transition_systems.append(hts)

        # Generate second models if any are necessary
        for problem in problems_config.problems:
            if problem.verification == VerificationType.EQUIVALENCE:
                if problem.equal_to is None:
                    raise RuntimeError("No second model for equivalence "
                                       "checking provided for problem {}".format(problem.name))

                hts2, _, _ = self.parse_model(problem.equal_to,
                                              problems_config.relative_path,
                                              general_config,
                                              "System 2",
                                              modifier)
                hierarchical_transition_systems.append(hts2)
                problems_config.add_second_model(problem, hts2)

        # TODO : contain these types of passes in functions
        #        they should be registered as passes
        # set default bit-wise initial values (0 or 1)
        if general_config.default_initial_value is not None:
            def_init_val = int(general_config.default_initial_value)
            try:
                if int(def_init_val) not in {0, 1}:
                    raise RuntimeError
            except:
                raise RuntimeError("Expecting 0 or 1 for default_initial_value,"
                                   "but received {}".format(def_init_val))
            def_init_ts = TS("Default initial values")
            new_init = []
            initialized_vars = get_free_variables(hts.single_init())
            state_vars = hts.state_vars
            num_def_init_vars = 0
            num_state_vars = len(state_vars)

            const_arr_supported = True

            if hts.logic == L_ABV:
                for p in problems_config.problems:
                    if p.solver_name not in CONST_ARRAYS_SUPPORT:
                        const_arr_supported = False
                        Logger.warning("Using default_initial_value with arrays, "
                                       "but one of the selected solvers, "
                                       "{} does not support constant arrays. "
                                       "Any assumptions on initial array values will "
                                       "have to be done manually".format(problem.solver_name))
                        break

            for sv in state_vars - initialized_vars:
                if sv.get_type().is_bv_type():
                    width = sv.get_type().width
                    if int(def_init_val) == 1:
                        val = BV((2**width)-1, width)
                    else:
                        val = BV(0, width)

                    num_def_init_vars += 1
                elif sv.get_type().is_array_type() and \
                     sv.get_type().elem_type.is_bv_type() and \
                     const_arr_supported:
                    svtype = sv.get_type()
                    width = svtype.elem_type.width
                    if int(def_init_val) == 1:
                        val = BV((2**width)-1, width)
                    else:
                        val = BV(0, width)
                    # create a constant array with a default value
                    val = Array(svtype.index_type, val)
                else:
                    continue

                def_init_ts.add_state_var(sv)
                new_init.append(EqualsOrIff(sv, val))
            def_init_ts.set_behavior(simplify(And(new_init)), TRUE(), TRUE())
            hts.add_ts(def_init_ts)
            Logger.msg("Set {}/{} state elements to zero "
                       "in initial state\n".format(num_def_init_vars, num_state_vars), 1)

        problems_config.hts = hts

        # TODO: Update this so that we can control whether embedded assertions are solved automatically
        for invar_prop in invar_props:
            problems_config.add_problem(verification=VerificationType.SAFETY,
                                        name=invar_prop[0],
                                        description=invar_prop[1],
                                        properties=invar_prop[2])
        for ltl_prop in ltl_props:
            problems_config.add_problem(verification=VerificationType.LTL,
                                        name=invar_prop[0],
                                        description=invar_prop[1],
                                        properties=invar_prop[2])

        Logger.log("Solving with abstract_clock=%s, add_clock=%s"%(general_config.abstract_clock,
                                                                   general_config.add_clock), 2)

        # ensure the miter_out variable exists
        miter_out = None

        for problem in problems_config.problems:
            if problem.name is not None:
                Logger.log("\n*** Analyzing problem \"%s\" ***"%(problem.name), 1)
                Logger.msg("Solving \"%s\" "%problem.name, 0, not(Logger.level(1)))

            # apply parametric behaviors (such as toggling the clock)
            # Note: This is supposed to be *before* creating the combined system for equivalence checking
            #       we want this assumption to be applied to both copies of the clock
            problem_hts = ParametricBehavior.apply_to_problem(problems_config.hts, problem, general_config, self.model_info)

            if problem.verification == VerificationType.EQUIVALENCE:
                hts2 = problems_config.get_second_model(problem)
                problem_hts, miter_out = Miter.combine_systems(hts,
                                                               hts2,
                                                               problem.bmc_length,
                                                               general_config.symbolic_init,
                                                               problem.properties,
                                                               True)

            try:
                # convert the formulas to PySMT FNodes
                # lemmas, assumptions and precondition always use the regular parser
                lemmas, assumptions, precondition = self.convert_formulae([problem.lemmas,
                                                                           problem.assumptions,
                                                                           problem.precondition],
                                                                          parser=self.sparser,
                                                                          relative_path=problems_config.relative_path)

                if problem.verification != VerificationType.LTL:
                    parser = self.sparser
                else:
                    parser = self.lparser

                prop = None
                if problem.properties is not None:
                    prop = self.convert_formula(problem.properties,
                                                relative_path=problems_config.relative_path,
                                                parser=parser)
                    assert len(prop) == 1, "Properties should already have been split into " \
                        "multiple problems but found {} properties here".format(len(prop))
                    prop = prop[0]
                else:
                    if problem.verification == VerificationType.SIMULATION:
                        prop = TRUE()
                    elif (problem.verification is not None) and (problem.verification != VerificationType.EQUIVALENCE):
                        Logger.error("Property not provided for problem {}".format(problem.name))

                if problem.verification == VerificationType.EQUIVALENCE:
                    assert miter_out is not None
                    # set property to be the miter output
                    # if user provided a different equivalence property, this has already
                    # been incorporated in the miter_out
                    prop = miter_out
                    # reset the miter output
                    miter_out = None

                if precondition:
                    assert len(precondition) == 1, "There should only be one precondition"
                    prop = Implies(precondition[0], prop)

                # TODO: keep assumptions separate from the hts
                # IMPORTANT: CLEAR ANY PREVIOUS ASSUMPTIONS AND LEMMAS
                #   This was previously done in __solve_problem and has been moved here
                #   during the frontend refactor in April 2019
                # this is necessary because the problem hts is just a reference to the
                #   overall (shared) HTS
                problem_hts.assumptions = None
                problem_hts.lemmas = None

                # Compute the Cone Of Influence
                # Returns a *new* hts (not pointing to the original one anymore)
                if problem.coi:
                    if Logger.level(2):
                        timer = Logger.start_timer("COI")
                    hts = self.coi.compute(hts, prop)
                    if Logger.level(2):
                        Logger.get_timer(timer)

                if general_config.time:
                    timer_solve = Logger.start_timer("Problem %s"%problem.name, False)

                status, trace, traces, region =  self.__solve_problem(problem_hts,
                                                              prop,
                                                              lemmas,
                                                              assumptions,
                                                              problem)

                # set status for this problem
                problems_config.set_problem_status(problem, status)

                # TODO: Determine whether we need both trace and traces
                assert trace is None or traces is None, "Expecting either a trace or a list of traces"
                if trace is not None:
                    problem_traces = self.__process_trace(hts, trace, general_config, problem)
                    problems_config.set_problem_traces(problem, problem_traces)

                if traces is not None:
                    traces_to_add = []
                    for trace in traces:
                        problem_trace = self.__process_trace(hts, trace, general_config, problem)
                        for pt in problem_trace:
                            traces_to_add.append(pt)
                    problems_config.set_problem_traces(problem, traces_to_add)

                if problem.verification == VerificationType.PARAMETRIC:
                    assert region is not None
                    problems_config.set_problem_region(problem, region)

                Logger.msg(" %s\n"%status, 0, not(Logger.level(1)))

                if (assume_if_true) and \
                   (status == VerificationStatus.TRUE) and \
                   (problem.assumptions == None) and \
                   (problem.verification == VerificationType.SAFETY):

                    # TODO: relax the assumption on problem.assumptions
                    #       can still add it, just need to make it an implication

                    ass_ts = TS("Previous assumption from property")
                    if TS.has_next(prop):
                        ass_ts.trans = prop
                    else:
                        ass_ts.invar = prop
                    # add assumptions to main system
                    problem_hts.reset_formulae()
                    problem_hts.add_ts(ass_ts)

                if general_config.time:
                    problems_config.set_problem_time(problem,
                                                     Logger.get_timer(timer_solve, False))

            except KeyboardInterrupt as e:
                Logger.msg("\b\b Skipped!\n", 0)


    def convert_formulae(self, formulae:List[Union[str, FNode]],
                         parser:Union[StringParser, LTLParser],
                         relative_path:Path=Path("."))->List[List[FNode]]:
        '''
        Converts string orepresentation of formulae to the internal representation
        of PySMT FNodes

        The string can also point to a file which contains string formulae, this
        method looks in the provided relative path for the formula file

        If passed None, it replace it with an empty list
        '''

        converted_formulae = [None]*len(formulae)
        for i in range(len(formulae)):
            if formulae[i] is not None:
                converted_formulae[i] = self.convert_formula(formulae[i], relative_path, parser)
            else:
                converted_formulae[i] = []

        return converted_formulae

    def convert_formula(self, formula:Union[str, FNode], relative_path:Path,
                        parser:Union[StringParser, LTLParser])->List[FNode]:

        if isinstance(formula, FNode):
            # TODO: There should be a better way to handle this nicely
            # Embedded assertions will likely be FNodes, but otherwise
            # they will be a property file or string
            return [formula]

        try:
            pdef_file = relative_path / formula
            with pdef_file.open() as f:
                # TODO: Update this to use a grammar or semi-colons
                # It would be nice to allow multi-line formulas
                # TODO: Find out if we even need all the tuple elements (only use the prop now)
                converted_tuples = parser.parse_formulae([p.strip() for p in f.read().strip().split("\n")])
        except OSError:
            converted_tuples = parser.parse_formulae([p.strip() for p in formula.split(MODEL_SP)])

        # extract the second tuple argument (the actual property)
        return [c[1] for c in converted_tuples]
