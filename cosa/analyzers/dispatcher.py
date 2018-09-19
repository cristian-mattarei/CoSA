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

from cosa.problem import VerificationType
from cosa.utils.logger import Logger
from cosa.analyzers.mcsolver import MCConfig
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationStatus, Trace
from cosa.encoders.miter import Miter
from cosa.encoders.formulae import StringParser
from cosa.representation import HTS, TS
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.symbolic_transition_system import SymbolicTSParser, SymbolicSimpleTSParser
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.ltl import LTLParser
from cosa.encoders.factory import ModelParsersFactory, GeneratorsFactory
from cosa.encoders.template import EncoderConfig, ModelInformation
from cosa.printers.trace import TextTracePrinter, VCDTracePrinter

FLAG_SR = "["
FLAG_ST = "]"
FLAG_SP = "+"

MODEL_SP = ";"
FILE_SP  = ","

class ProblemSolver(object):
    parser = None
    sparser = None
    lparser = None
    model_info = None

    def __init__(self):
        self.sparser = None
        self.lparser = None
        self.model_info = ModelInformation()

    def __process_trace(self, hts, trace, config, problem):
        prevass = []

        full_trace = problem.full_trace or config.full_trace
        trace_vars_change = problem.trace_vars_change or config.trace_vars_change
        trace_all_vars = problem.trace_all_vars or config.trace_all_vars

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
        
        mc_config = self.problem2mc_config(problem, config)
        bmc_safety = BMCSafety(problem.hts, mc_config)
        bmc_ltl = BMCLTL(problem.hts, mc_config)
        res = VerificationStatus.UNC
        bmc_length = max(problem.bmc_length, config.bmc_length)
        bmc_length_min = max(problem.bmc_length_min, config.bmc_length_min)

        parsing_defs = [mc_config.properties, mc_config.lemmas, mc_config.assumptions]
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

        [mc_config.properties, mc_config.lemmas, mc_config.assumptions] = parsing_defs

        if problem.generators is not None:

            varsdict = dict([(var.symbol_name(), var) for var in problem.hts.vars])
            
            for strgenerator in problem.generators.split(MODEL_SP):
                strgenerator = strgenerator.replace(" ","")
                if strgenerator == "":
                    continue

                eqpos = strgenerator.find("=")
                parstart = strgenerator.find("(")
                if (parstart < eqpos) or (eqpos == -1):
                    Logger.error("Invalid generators")

                instance = strgenerator[:eqpos:]
                mdef = strgenerator[eqpos+1:]
                mtype = mdef.split("(")[0]
                pars = mdef[mdef.find("(")+1:-1].split(",")
                generator = GeneratorsFactory.generator_by_name(mtype)
                pars = [varsdict[v] if v in varsdict else v for v in pars]
                ts = generator.get_sts(instance, pars)

                problem.hts.add_ts(ts)
        
        assumps = None
        lemmas = None

        if mc_config.properties is None:
            if problem.verification == VerificationType.SIMULATION:
                mc_config.properties = ["True"]
            elif (problem.verification is not None) and (problem.verification != VerificationType.EQUIVALENCE):
                Logger.error("Property not provided")
                
        accepted_ver = False

        if (problem.verification != VerificationType.EQUIVALENCE) and (mc_config.properties is not None):
            assumps = [t[1] for t in self.sparser.parse_formulae(mc_config.assumptions)]
            lemmas = [t[1] for t in self.sparser.parse_formulae(mc_config.lemmas)]
            for ass in assumps:
                problem.hts.add_assumption(ass)
            for lemma in lemmas:
                problem.hts.add_lemma(lemma)
            if problem.verification != VerificationType.LTL:
                (strprop, prop, types) = self.sparser.parse_formulae(mc_config.properties)[0]
            else:
                (strprop, prop, types) = self.lparser.parse_formulae(mc_config.properties)[0]

            problem.formula = prop

        if problem.verification is None:
            return problem
            
        if problem.verification == VerificationType.SAFETY:
            accepted_ver = True
            Logger.log("Property: %s"%(prop.serialize(threshold=100)), 2)
            res, trace, _ = bmc_safety.safety(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.LTL:
            accepted_ver = True
            res, trace, _ = bmc_ltl.ltl(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.SIMULATION:
            accepted_ver = True
            res, trace = bmc_safety.simulate(prop, bmc_length)

        hts = problem.hts
            
        if problem.verification == VerificationType.EQUIVALENCE:
            accepted_ver = True
            if problem.equivalence:
                (problem.hts2, _, _) = self.parse_model(problem.relative_path, \
                                                        problem.equivalence, \
                                                        encoder_config, \
                                                        "System 2")

            htseq, miter_out = Miter.combine_systems(problem.hts, \
                                                     problem.hts2, \
                                                     bmc_length, \
                                                     problem.symbolic_init, \
                                                     mc_config.properties, \
                                                     True)

            if mc_config.assumptions is not None:
                assumps = [t[1] for t in self.sparser.parse_formulae(mc_config.assumptions)]

            if mc_config.lemmas is not None:
                lemmas = [t[1] for t in self.sparser.parse_formulae(mc_config.lemmas)]

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

        if problem.assumptions is not None:
            problem.hts.assumptions = None

        Logger.log("\n*** Problem \"%s\" is %s ***"%(problem, res), 1)

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)
        
        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)
        
    def parse_model(self, \
                    relative_path, \
                    model_files, \
                    encoder_config, \
                    name=None):
        
        hts = HTS("System 1")
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

                Logger.msg("Parsing file \"%s\"... "%(strfile), 0)
                (hts_a, inv_a, ltl_a) = parser.parse_file(strfile, encoder_config, flags)
                self.model_info.combine(parser.get_model_info())
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
        if len(problems.problems) == 0:
            Logger.error("No problems defined")
            
        encoder_config = self.problems2encoder_config(config, problems)

        self.sparser = StringParser(encoder_config)
        self.lparser = LTLParser()
        
        # generate systems for each problem configuration
        systems = {}
        for si in problems.symbolic_inits:
            encoder_config.symbolic_init = si
            (systems[('hts', si)], _, _) = self.parse_model(problems.relative_path, \
                                                            problems.model_file, \
                                                            encoder_config, # si,\
                                                            "System 1")

        if problems.equivalence is not None:
            (systems[('hts2', si)], _, _) = self.parse_model(problems.relative_path, \
                                                             problems.equivalence, \
                                                             encoder_config, #si, \
                                                             "System 2")
        else:
            systems[('hts2', si)] = None

        assume_if_true = config.assume_if_true or problems.assume_if_true
        
        for problem in problems.problems:
            problem.hts = systems[('hts', problem.symbolic_init)]
            problem.hts2 = systems[('hts2', problem.symbolic_init)]
            problem.abstract_clock = problems.abstract_clock
            problem.add_clock = problems.add_clock
            problem.run_coreir_passes = problems.run_coreir_passes
            problem.relative_path = problems.relative_path

            if not problem.full_trace:
                problem.full_trace = problems.full_trace
            if not problem.trace_vars_change:
                problem.trace_vars_change = problems.trace_vars_change
            if not problem.trace_all_vars:
                problem.trace_all_vars = problems.trace_all_vars

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
        mc_config.vcd_trace = problem.vcd or config.vcd
        mc_config.prove = config_selection(problem.prove, config.prove)
        mc_config.properties = problem.formula
        mc_config.assumptions = problem.assumptions
        mc_config.lemmas = problem.lemmas

        return mc_config


    def problems2encoder_config(self, config, problems):
        encoder_config = EncoderConfig()
        encoder_config.abstract_clock = problems.abstract_clock
        encoder_config.symbolic_init = config.symbolic_init
        encoder_config.zero_init = problems.zero_init or config.zero_init
        encoder_config.add_clock = problems.add_clock
        encoder_config.deterministic = config.deterministic
        encoder_config.run_passes = config.run_passes
        encoder_config.boolean = problems.boolean

        return encoder_config
        
