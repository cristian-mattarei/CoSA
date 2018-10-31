# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os
import copy

import pickle

from pysmt.shortcuts import Symbol

from cosa.utils.logger import Logger
from cosa.analyzers.mcsolver import MCConfig
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_parametric import BMCParametric
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationType, Problem, VerificationStatus, Trace
from cosa.encoders.miter import Miter
from cosa.encoders.formulae import StringParser
from cosa.representation import HTS, TS
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

        full_trace = problem.full_trace or config.full_trace
        trace_vars_change = problem.trace_vars_change or config.trace_vars_change
        trace_all_vars = problem.trace_all_vars or config.trace_all_vars
        trace_values_base = problem.trace_values_base or config.trace_values_base

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
        if problem.vcd:
            vcd_printer = VCDTracePrinter()
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

    def __solve_problem(self, problem, config):
        if problem.name is not None:
            Logger.log("\n*** Analyzing problem \"%s\" ***"%(problem), 1)
            Logger.msg("Solving \"%s\" "%problem.name, 0, not(Logger.level(1)))


        parsing_defs = [problem.formula, problem.lemmas, problem.assumptions]
        for i in range(len(parsing_defs)):
            if parsing_defs[i] is not None:
                pdef_file = problem.relative_path+parsing_defs[i]
                if os.path.isfile(pdef_file):
                    with open(pdef_file) as f:
                        parsing_defs[i] = [p.strip() for p in f.read().strip().split("\n")]
                else:
                    parsing_defs[i] = [p.strip() for p in parsing_defs[i].split(MODEL_SP)]
            else:
                parsing_defs[i] = None

        [formulae, problem.lemmas, problem.assumptions] = parsing_defs

        ParametricBehavior.apply_to_problem(problem, self.model_info)

        assumps = None
        lemmas = None

        trace = None
        traces = None
        
        if formulae is None:
            if problem.verification == VerificationType.SIMULATION:
                formulae = ["True"]
            elif (problem.verification is not None) and (problem.verification != VerificationType.EQUIVALENCE):
                Logger.error("Property not provided")
                
        accepted_ver = False

        if formulae is not None:
            problem.formula = formulae[0]
        
        precondition = config.precondition if config.precondition is not None else problem.precondition

        if precondition and problem.verification == VerificationType.SAFETY:
            problem.formula = "(%s) -> (%s)"%(precondition, problem.formula)
        
        if (problem.verification != VerificationType.EQUIVALENCE) and (problem.formula is not None):
            assumps = [t[1] for t in self.sparser.parse_formulae(problem.assumptions)]
            lemmas = [t[1] for t in self.sparser.parse_formulae(problem.lemmas)]
            for ass in assumps:
                problem.hts.add_assumption(ass)
            for lemma in lemmas:
                problem.hts.add_lemma(lemma)
            if problem.verification != VerificationType.LTL:
                (strprop, prop, types) = self.sparser.parse_formulae([problem.formula])[0]
            else:
                (strprop, prop, types) = self.lparser.parse_formulae([problem.formula])[0]

            problem.formula = prop

        if problem.verification is None:
            return problem

        if problem.coi:
            if Logger.level(2):
                timer = Logger.start_timer("COI")
            problem.hts = self.coi.compute(problem.hts, problem.formula)
            if Logger.level(2):
                Logger.get_timer(timer)

        mc_config = self.problem2mc_config(problem, config)
        bmc_safety = BMCSafety(problem.hts, mc_config)
        bmc_parametric = BMCParametric(problem.hts, mc_config)
        bmc_ltl = BMCLTL(problem.hts, mc_config)
        res = VerificationStatus.UNC
        bmc_length = max(problem.bmc_length, config.bmc_length)
        bmc_length_min = max(problem.bmc_length_min, config.bmc_length_min)

        
        if problem.verification == VerificationType.SAFETY:
            accepted_ver = True
            Logger.log("Property: %s"%(prop.serialize(threshold=100)), 2)
            res, trace, _ = bmc_safety.safety(prop, bmc_length, bmc_length_min, config.processes)

        if problem.verification == VerificationType.LTL:
            accepted_ver = True
            res, trace, _ = bmc_ltl.ltl(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.SIMULATION:
            accepted_ver = True
            res, trace = bmc_safety.simulate(prop, bmc_length)

        if problem.verification == VerificationType.PARAMETRIC:
            accepted_ver = True
            Logger.log("Property: %s"%(prop.serialize(threshold=100)), 2)
            res, traces, problem.region = bmc_parametric.parametric_safety(prop, bmc_length, bmc_length_min, ModelExtension.get_parameters(problem.hts), at_most=problem.cardinality)
            
        hts = problem.hts

        if problem.verification == VerificationType.EQUIVALENCE:
            accepted_ver = True
            htseq, miter_out = Miter.combine_systems(problem.hts, \
                                                     problem.hts2, \
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

            bmcseq = BMCSafety(htseq, mc_config)
            hts = htseq
            res, trace, t = bmcseq.safety(miter_out, bmc_length, bmc_length_min)

        if not accepted_ver:
            Logger.error("Invalid verification type")
            
        problem.status = res
        if trace is not None:
            problem.traces = self.__process_trace(hts, trace, config, problem)

        if traces is not None:
            problem.traces = []
            for trace in traces:
                problem.traces += self.__process_trace(hts, trace, config, problem)

        if problem.assumptions is not None:
            problem.hts.assumptions = None

        Logger.log("\n*** Problem \"%s\" is %s ***"%(problem, res), 1)

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)
        
        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)

    def md5(self, fname):
        import hashlib
        hash_md5 = hashlib.md5()
        with open(fname, "rb") as f:
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
                    model_files, \
                    encoder_config, \
                    name=None, \
                    modifier=None, \
                    cache_files=False, \
                    clean_cache=False):
        
        hts = HTS(name if name is not None else "System")
        invar_props = []
        ltl_props = []

        models = model_files.split(FILE_SP)

        for strfile in models:
            (strfile, flags) = self.get_file_flags(strfile)
            filetype = strfile.split(".")[-1]
            strfile = strfile.replace("~", os.path.expanduser("~"))
            if strfile[0] != "/":
                strfile = relative_path+strfile
            parser = None

            for av_parser in ModelParsersFactory.get_parsers():
                assert av_parser.name is not None
                if filetype in av_parser.get_extensions():
                    parser = av_parser
                    if not self.parser:
                        self.parser = av_parser
                    
            if parser is not None:
                if not os.path.isfile(strfile):
                    Logger.error("File \"%s\" does not exist"%strfile)

                if cache_files:
                    md5 = self.md5(strfile)
                    cf = "-".join(["1" if encoder_config.abstract_clock else "0", \
                                   "1" if encoder_config.add_clock else "0", \
                                   "1" if encoder_config.boolean else "0"])
                    cachefile = "%s-%s"%(md5, cf)
                    cachedir = "%s/%s"%("/".join(strfile.split("/")[:-1]), COSACACHEDIR)
                
                if cache_files and self._is_cached(cachedir, cachefile, clean_cache):
                    Logger.msg("Loading from cache file \"%s\"... "%(strfile), 0)
                    (hts_a, inv_a, ltl_a, model_info) = self._from_cache(cachedir, cachefile, encoder_config, flags)
                else:
                    Logger.msg("Parsing file \"%s\"... "%(strfile), 0)
                    (hts_a, inv_a, ltl_a) = parser.parse_file(strfile, encoder_config, flags)

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

    def solve_problems(self, problems, config):
        encoder_config = self.problems2encoder_config(config, problems)

        self.sparser = StringParser(encoder_config)
        self.lparser = LTLParser()

        self.coi = ConeOfInfluence()
        
        invar_props = []
        ltl_props = []
        si = False

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

    def problem2mc_config(self, problem, config):
        mc_config = MCConfig()

        config_selection = lambda problem, config: config if problem is None else problem
        
        mc_config.smt2file = config_selection(problem.smt2_tracing, config.smt2file)
        mc_config.prefix = problem.name
        mc_config.strategy = config_selection(problem.strategy, config.strategy)
        mc_config.incremental = config_selection(problem.incremental, config.incremental)
        mc_config.skip_solving = config_selection(problem.skip_solving, config.skip_solving)
        mc_config.solver_name = config_selection(problem.solver_name, config.solver_name)
        mc_config.prove = config_selection(problem.prove, config.prove)

        return mc_config


    def problems2encoder_config(self, config, problems):
        encoder_config = EncoderConfig()
        encoder_config.abstract_clock = problems.abstract_clock or config.abstract_clock
        encoder_config.symbolic_init = config.symbolic_init or config.symbolic_init
        encoder_config.zero_init = problems.zero_init or config.zero_init
        encoder_config.add_clock = problems.add_clock or config.add_clock
        encoder_config.deterministic = config.deterministic
        encoder_config.run_passes = config.run_passes
        encoder_config.boolean = problems.boolean or config.boolean
        encoder_config.devel = config.devel

        return encoder_config
       
 
