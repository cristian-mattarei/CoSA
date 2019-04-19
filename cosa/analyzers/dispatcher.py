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
from cosa.analyzers.mcsolver import MCConfig, CONST_ARRAYS_SUPPORT
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_parametric import BMCParametric
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationType, Problem, VerificationStatus, Trace
from cosa.encoders.miter import Miter
from cosa.encoders.formulae import StringParser
from cosa.representation import HTS, TS, L_ABV
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.ltl import LTLParser
from cosa.encoders.factory import ModelParsersFactory, ClockBehaviorsFactory, GeneratorsFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.modifiers.coi import ConeOfInfluence
from cosa.encoders.template import EncoderConfig, ModelInformation
from cosa.encoders.parametric_behavior import ParametricBehavior
from cosa.printers.trace import TextTracePrinter, VCDTracePrinter
from cosa.modifiers.model_extension import ModelExtension
from cosa.encoders.symbolic_transition_system import SymbolicSimpleTSParser
from cosa.printers.factory import HTSPrintersFactory
from cosa.printers.hts import STSHTSPrinter
from cosa.problem import ProblemsManager


FLAG_SR = "["
FLAG_ST = "]"
FLAG_SP = "+"

MODEL_SP = ";"
FILE_SP  = ","

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

        full_trace = config.full_trace
        trace_vars_change = config.trace_vars_change
        trace_all_vars = config.trace_all_vars
        trace_values_base = config.trace_values_base

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

        if problem.name is not None:
            Logger.log("\n*** Analyzing problem \"%s\" ***"%(problem.name), 1)
            Logger.msg("Solving \"%s\" "%problem.name, 0, not(Logger.level(1)))

        trace = None
        traces = None

        # TODO Move this somewhere earlier
        if prop is None:
            if problem.verification == VerificationType.SIMULATION:
                prop = TRUE()
            elif (problem.verification is not None) and (problem.verification != VerificationType.EQUIVALENCE):
                Logger.error("Property not provided")

        accepted_ver = False

        if (problem.verification != VerificationType.EQUIVALENCE) and (prop is not None):
            assert hts.assumptions is None, "There should not be any left-over assumptions from previous problems"
            for assump in assumptions:
                hts.add_assumption(assump)
            for lemma in lemmas:
                hts.add_lemma(lemma)

        # TODO: make sure this case can be removed
        # if problem.verification is None:
        #     return problem

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
            res, traces, problem.region = bmc_parametric.parametric_safety(prop, bmc_length, bmc_length_min, ModelExtension.get_parameters(hts), at_most=problem.cardinality)

        # TODO: Enable this again
        # TODO: add hts2 to interface, or bundle things somehow
        if problem.verification == VerificationType.EQUIVALENCE:
            raise RuntimeError("Equivalence not currently supported -- needs to be re-enabled")
            accepted_ver = True
            htseq, miter_out = Miter.combine_systems(hts, \
                                                     hts2, \
                                                     bmc_length, \
                                                     problem.symbolic_init, \
                                                     problem.formula, \
                                                     True)

            if problem.assumptions is not None:
                assumps = [t[1] for t in self.sparser.parse_formulae(problem.assumptions)]

            if problem.lemmas is not None:
                lemmas = [t[1] for t in self.sparser.parse_formulae(problem.lemmas)]

            if assumps is not None:
                for assumption in assumps:
                    htseq.add_assumption(assumption)

            if lemmas is not None:
                for lemma in lemmas:
                    htseq.add_lemma(lemma)

            bmcseq = BMCSafety(htseq, problem)
            hts = htseq
            res, trace, t = bmcseq.safety(miter_out, bmc_length, bmc_length_min)

        if not accepted_ver:
            Logger.error("Invalid verification type")

        Logger.log("\n*** Problem \"%s\" is %s ***"%(problem, res), 1)
        return res, trace, traces

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)

        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)

    def md5(self, fname:Path):
        import hashlib
        hash_md5 = hashlib.md5()
        with fname.open() as f:
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
                    relative_path, \
                    general_config, \
                    name=None, \
                    modifier=None):

        hts = HTS(name if name is not None else "System")
        invar_props = []
        ltl_props = []

        models = general_config.model_file.split(FILE_SP)
        cache_files = general_config.cache_files
        clean_cache = general_config.clean_cache

        for strfile in models:
            (strfile, flags) = self.get_file_flags(strfile)
            if len(strfile) > 1 and strfile[:2] == '~/':
                filepath = Path.home() / Path(strfile[2:])
            else:
                filepath = Path(strfile)
            if filepath.parts[0] != "/":
                strfile = relative_path / filepath
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

    def solve_problems_new(self, problems_config:ProblemsManager)->None:

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

        # generate system
        hts, invar_props, ltl_props = self.parse_model(problems_config.relative_path,
                                                       general_config,
                                                       "System 1",
                                                       modifier)

        # TODO: test this
        if model_extension:
            hts = ParametricBehavior.apply_to_problem(hts, problem, self.model_info)

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

        # TODO: Handle equivalence gracefully
        #       should be able to specify this per-problem
        #       requires generating systems for each one

        # if general_config.equivalence is not None:
        #     hts2, _, _ = self.parse_model(problems_config.relative_path,
        #                                   general_config,
        #                                   "System 2",
        #                                   modifier)
        #     problems_config.hts2 = hts2

        # TODO: Update this so that we can control whether embedded assertions are solved automatically
        for invar_prop in invar_props:
            inv_prob = problems.new_problem(verification=VerificationType.SAFETY,
                                            name=invar_prop[0],
                                            description=invar_prop[1],
                                            formula=invar_prop[2])

        for ltl_prop in ltl_props:
            inv_prob = problems.new_problem(verification=VerificationType.LTL,
                                            name=invar_prop[0],
                                            description=invar_prop[1],
                                            formula=invar_prop[2])

        Logger.log("Solving with abstract_clock=%s, add_clock=%s"%(general_config.abstract_clock,
                                                                   general_config.add_clock), 2)
        for problem in problems_config.problems:
            problem_hts = problems_config.hts

            # TODO fix this -- see comment about equivalence above
            if problem.verification == VerificationType.EQUIVALENCE:
                raise RuntimeError("Equivalence currently unsupported")

            # TODO: Do this somewhere else, these problems aren't modifiable anymore
            # if problem.trace_prefix is not None:
            #     problem.trace_prefix = "".join([problem.relative_path,problem.trace_prefix])
            if general_config.time:
                timer_solve = Logger.start_timer("Problem %s"%problem.name, False)
            try:
                # convert the formulas to PySMT FNodes
                prop, lemmas, assumptions, precondition = self.convert_formulae([problem.properties,
                                                                                    problem.lemmas,
                                                                                    problem.assumptions,
                                                                                    problem.precondition],
                                                                                   verification_type=problem.verification,
                                                                                   relative_path=problems_config.relative_path)

                # # TODO: Update this to allow splitting problems
                if len(prop) > 1:
                    raise RuntimeError("Expecting a single formula "
                                       "per problem but got {}".format(prop))
                prop = prop[0]

                if precondition and problem.verification == VerificationType.SAFETY:
                    prop = Implies(precondition, prop)

                # TODO: keep assumptions separate from the hts
                # IMPORTANT: CLEAR ANY PREVIOUS ASSUMPTIONS AND LEMMAS
                #   This was previously done in __solve_problems and has been moved here
                #   during the frontend refactor in April 2019
                # this is necessary because the problem hts is just a reference to the
                #   overall (shared) HTS
                problems_config.hts.assumptions = None
                problems_config.hts.lemmas = None

                # Compute the Cone Of Influence
                # Returns a *new* hts (not pointing to the original one anymore)
                if problem.coi:
                    if Logger.level(2):
                        timer = Logger.start_timer("COI")
                    hts = self.coi.compute(hts, prop)
                    if Logger.level(2):
                        Logger.get_timer(timer)


                # TODO: make sure we don't need general_config
                # as a design rule, we shouldn't -- this is just about the problem now
                status, trace, traces =  self.__solve_problem(problem_hts,
                                                              prop,
                                                              lemmas,
                                                              assumptions,
                                                              problem)

                # set status for this problem
                problems_config.set_problem_status(problem, status)

                # TODO: Determine whether we need both trace and traces
                if trace is not None:
                    problem_traces = self.__process_trace(hts, trace, general_config, problem)
                    problems_config.set_problem_traces(problem, problem_traces)

                if traces is not None:
                    problem_traces = []
                    for trace in traces:
                        problem_traces.append(self.__process_trace(hts, trace, general_config, problem))
                    problems_config.set_problem_traces(problem, problem_traces)

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
                    problems_config.hts.reset_formulae()
                    problems_config.hts.add_ts(ass_ts)

                if general_config.time:
                    problems_config.set_problem_time(problem,
                                                     Logger.get_timer(timer_solve, False))

            except KeyboardInterrupt as e:
                Logger.msg("\b\b Skipped!\n", 0)


    def convert_formulae(self, formulae:List[Union[str, FNode]],
                         verification_type:str,
                         relative_path:Path=Path(".")):
        '''
        Converts string representation of formulae to the internal representation
        of PySMT FNodes

        The string can also point to a file which contains string formulae, this
        method looks in the provided relative path for the formula file

        If passed None, it replace it with an empty list
        '''

        if verification_type != VerificationType.LTL:
            parser = self.sparser
        else:
            parser = self.lparser

        converted_formulae = [None]*len(formulae)
        for i in range(len(formulae)):
            if formulae[i] is not None:
                if isinstance(formulae[i], FNode):
                    # TODO: There should be a better way to handle this nicely
                    # Embedded assertions will likely be FNodes, but otherwise
                    # they will be a property file or string
                    converted_formulae[i] = [formulae[i]]
                    continue

                pdef_file = relative_path / formulae[i]
                if pdef_file.is_file():
                    with pdef_file.open() as f:
                        # TODO: Update this to use a grammar or semi-colons
                        # It would be nice to allow multi-line formulas

                        # TODO: Find out if we even need all the tuple elements (only use the prop now)
                        converted_tuples = parser.parse_formulae([p.strip() for p in f.read().strip().split("\n")])
                else:
                    converted_tuples = parser.parse_formulae([p.strip() for p in formulae[i].split(MODEL_SP)])

                # extract the second tuple argument (the actual property)
                converted_formulae[i] = [c[1] for c in converted_tuples]
            else:
                converted_formulae[i] = []

        return converted_formulae


    def solve_problems(self, problems, config):
        encoder_config = self.problems2encoder_config(config, problems)

        self.sparser = StringParser(encoder_config)
        self.lparser = LTLParser()

        self.coi = ConeOfInfluence()

        invar_props = []
        ltl_props = []
        si = (config.symbolic_init | problems.symbolic_init)

        if len(problems.symbolic_inits) == 0:
            problems.symbolic_inits.add(si)

        HTSM = 0
        HTS2 = 1
        HTSD = (HTSM, si)

        model_extension = config.model_extension if problems.model_extension is None else problems.model_extension
        assume_if_true = config.assume_if_true or problems.assume_if_true
        cache_files = config.cache_files or problems.cache_files
        clean_cache = config.clean_cache

        modifier = None
        if model_extension is not None:
            modifier = lambda hts: ModelExtension.extend(hts, ModelModifiersFactory.modifier_by_name(model_extension))

        # generate systems for each problem configuration
        systems = {}
        for si in problems.symbolic_inits:
            encoder_config.symbolic_init = si
            (systems[(HTSM, si)], invar_props, ltl_props) = self.parse_model(problems.relative_path, \
                                                                             problems.model_file, \
                                                                             encoder_config, \
                                                                             "System 1", \
                                                                             modifier, \
                                                                             cache_files=cache_files, \
                                                                             clean_cache=clean_cache)

        if problems.equivalence is not None:
            (systems[(HTS2, si)], _, _) = self.parse_model(problems.relative_path, \
                                                           problems.equivalence, \
                                                           encoder_config, \
                                                           "System 2", \
                                                           cache_files=cache_files, \
                                                           clean_cache=clean_cache)
        else:
            systems[(HTS2, si)] = None

        if config.safety or config.problems:
            for invar_prop in invar_props:
                inv_prob = problems.new_problem()
                inv_prob.verification = VerificationType.SAFETY
                inv_prob.name = invar_prop[0]
                inv_prob.description = invar_prop[1]
                inv_prob.formula = invar_prop[2]
                problems.add_problem(inv_prob)

        if config.ltl or config.problems:
            for ltl_prop in ltl_props:
                ltl_prob = problems.new_problem()
                ltl_prob.verification = VerificationType.LTL
                ltl_prob.name = ltl_prop[0]
                ltl_prob.description = ltl_prop[1]
                ltl_prob.formula = ltl_prop[2]
                problems.add_problem(ltl_prob)

        if HTSD in systems:
            problems._hts = systems[HTSD]

        for problem in problems.problems:
            problem.hts = systems[(HTSM, problem.symbolic_init)]

            if problems._hts is None:
                problems._hts = problem.hts
            problem.hts2 = systems[(HTS2, problem.symbolic_init)]
            if problems._hts2 is None:
                problems._hts2 = problem.hts2
            problem.vcd = problems.vcd or config.vcd or problem.vcd
            problem.abstract_clock = problems.abstract_clock or config.abstract_clock
            problem.add_clock = problems.add_clock or config.add_clock
            problem.coi = problems.coi or config.coi
            problem.run_coreir_passes = problems.run_coreir_passes
            problem.relative_path = problems.relative_path
            problem.cardinality = max(problems.cardinality, config.cardinality)

            if not problem.full_trace:
                problem.full_trace = problems.full_trace
            if not problem.trace_vars_change:
                problem.trace_vars_change = problems.trace_vars_change
            if not problem.trace_all_vars:
                problem.trace_all_vars = problems.trace_all_vars
            if not problem.clock_behaviors:
                clk_bhvs = [p for p in [problems.clock_behaviors, config.clock_behaviors] if p is not None]
                if len(clk_bhvs) > 0:
                    problem.clock_behaviors = ";".join(clk_bhvs)
            if not problem.generators:
                problem.generators = config.generators

            Logger.log("Solving with abstract_clock=%s, add_clock=%s"%(problem.abstract_clock, problem.add_clock), 2)

            if problem.trace_prefix is not None:
                problem.trace_prefix = "".join([problem.relative_path,problem.trace_prefix])

            if config.time or problems.time:
                timer_solve = Logger.start_timer("Problem %s"%problem.name, False)
            try:
                self.__solve_problem(problem, config)

                if problem.verification is None:
                    Logger.log("Unset verification", 2)
                    continue

                Logger.msg(" %s\n"%problem.status, 0, not(Logger.level(1)))

                if (assume_if_true) and \
                   (problem.status == VerificationStatus.TRUE) and \
                   (problem.assumptions == None) and \
                   (problem.verification == VerificationType.SAFETY):

                    ass_ts = TS("Previous assumption from property")
                    if TS.has_next(problem.formula):
                        ass_ts.trans = problem.formula
                    else:
                        ass_ts.invar = problem.formula
                    problem.hts.reset_formulae()

                    problem.hts.add_ts(ass_ts)

                if config.time or problems.time:
                    problem.time = Logger.get_timer(timer_solve, False)

            except KeyboardInterrupt as e:
                Logger.msg("\b\b Skipped!\n", 0)

    # FIXME: remove this with new frontend -- just use problem object directly
    def problem2mc_config(self, problem, config):
        mc_config = MCConfig()

        config_selection = lambda problem, config: config if problem is None else problem

        mc_config.smt2_tracing = config_selection(problem.smt2_tracing, config.smt2_tracing)
        mc_config.prefix = problem.name
        mc_config.strategy = config_selection(problem.strategy, config.strategy)
        mc_config.incremental = config_selection(problem.incremental, config.incremental)
        mc_config.skip_solving = config_selection(problem.skip_solving, config.skip_solving)
        mc_config.solver_name = config_selection(problem.solver_name, config.solver_name)
        mc_config.solver_options = config_selection(problem.solver_options, config.solver_options)
        mc_config.prove = config_selection(problem.prove, config.prove)

        return mc_config

    # FIXME: remove this with new frontend
    def problems2encoder_config(self, config, problems):
        encoder_config = EncoderConfig()
        encoder_config.abstract_clock = problems.abstract_clock or config.abstract_clock
        encoder_config.symbolic_init = config.symbolic_init or config.symbolic_init
        encoder_config.zero_init = problems.zero_init or config.zero_init
        encoder_config.add_clock = problems.add_clock or config.add_clock
        encoder_config.deterministic = config.deterministic
        encoder_config.run_coreir_passes = config.run_coreir_passes
        encoder_config.boolean = problems.boolean or config.boolean
        encoder_config.devel = config.devel
        encoder_config.opt_circuit = problems.opt_circuit or config.opt_circuit
        encoder_config.no_arrays = problems.no_arrays or config.no_arrays

        return encoder_config
