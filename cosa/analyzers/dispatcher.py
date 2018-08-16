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
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.encoders.coreir import CoreIRParser
from cosa.analyzers.mcsolver import MCConfig
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationStatus
from cosa.encoders.miter import Miter
from cosa.representation import HTS
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.symbolic_transition_system import SymbolicTSParser, SymbolicSimpleTSParser
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.ltl import ltl_reset_env, LTLParser
from cosa.encoders.monitors import MonitorsFactory

FLAG_SR = "["
FLAG_ST = "]"
FLAG_SP = "+"

MODEL_SP = ","

class ProblemSolver(object):
    parser = None

    def __init__(self):
        pass

    def solve_problem(self, problem, config):
        Logger.log("\n*** Analyzing problem \"%s\" ***"%(problem), 1)
        Logger.msg("Solving \"%s\" "%problem.name, 0, not(Logger.level(1)))
        
        sparser = StringParser()
        lparser = LTLParser()

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

        assumps = None
        lemmas = None

        accepted_ver = False

        if problem.monitors is not None:

            varsdict = dict([(var.symbol_name(), var) for var in problem.hts.vars])
            
            for strmonitor in problem.monitors.split(")"):
                strmonitor = strmonitor.replace(" ","")
                if strmonitor == "":
                    continue
                instance, mtype = strmonitor.split("=")
                mtype, pars = mtype.split("(")
                pars = pars.split(",")

                monitor = MonitorsFactory.monitor_by_name(mtype)
                pars = [varsdict[v] if v in varsdict else v for v in pars]
                ts = monitor.get_sts(instance, pars)

                problem.hts.add_ts(ts)
                
        if problem.verification != VerificationType.EQUIVALENCE:
            assumps = [t[1] for t in sparser.parse_formulae(mc_config.assumptions)]
            lemmas = [t[1] for t in sparser.parse_formulae(mc_config.lemmas)]
            for ass in assumps:
                problem.hts.add_assumption(ass)
            for lemma in lemmas:
                problem.hts.add_lemma(lemma)
            if problem.verification != VerificationType.LTL:
                (strprop, prop, types) = sparser.parse_formulae(mc_config.properties)[0]
            else:
                (strprop, prop, types) = lparser.parse_formulae(mc_config.properties)[0]

        if problem.verification == VerificationType.SAFETY:
            accepted_ver = True
            res, trace, _ = bmc_safety.safety(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.LTL:
            accepted_ver = True
            res, trace, _ = bmc_ltl.ltl(prop, bmc_length, bmc_length_min)

        if problem.verification == VerificationType.SIMULATION:
            accepted_ver = True
            res, trace = bmc_safety.simulate(prop, bmc_length)
            
        if problem.verification == VerificationType.EQUIVALENCE:
            accepted_ver = True
            if problem.equivalence:
                (problem.hts2, _, _) = self.parse_model(problem.relative_path, problem.equivalence, problem.abstract_clock, problem.symbolic_init, "System 2", no_clock=problem.no_clock)

            htseq, miter_out = Miter.combine_systems(problem.hts, problem.hts2, bmc_length, problem.symbolic_init, mc_config.properties, True)

            if mc_config.assumptions is not None:
                assumps = [t[1] for t in sparser.parse_formulae(mc_config.assumptions)]

            if mc_config.lemmas is not None:
                lemmas = [t[1] for t in sparser.parse_formulae(mc_config.lemmas)]

            if assumps is not None:
                for assumption in assumps:
                    htseq.add_assumption(assumption)

            if lemmas is not None:
                for lemma in lemmas:
                    htseq.add_lemma(lemma)

            bmcseq = BMCSafety(htseq, mc_config)
            res, trace, t = bmcseq.safety(miter_out, bmc_length, bmc_length_min)

        if not accepted_ver:
            Logger.error("Invalid verification type")
            
        problem.status = res
        problem.trace = trace

        if problem.assumptions is not None:
            problem.hts.assumptions = None

        Logger.log("\n*** Problem \"%s\" is %s ***"%(problem, res), 1)

    def get_file_flags(self, strfile):
        if FLAG_SR not in strfile:
            return (strfile, None)
        
        (strfile, flags) = (strfile[:strfile.index(FLAG_SR)], strfile[strfile.index(FLAG_SR)+1:strfile.index(FLAG_ST)].split(FLAG_SP))
        return (strfile, flags)
        
    def parse_model(self, relative_path, model_files, abstract_clock, symbolic_init, name=None, deterministic=False, boolean=False, no_clock=False):
        hts = HTS("System 1")
        invar_props = []
        ltl_props = []

        models = model_files.split(MODEL_SP)

        for strfile in models:
            (strfile, flags) = self.get_file_flags(strfile)
            filetype = strfile.split(".")[-1]
            strfile = strfile.replace("~", os.path.expanduser("~"))
            if strfile[0] != "/":
                strfile = relative_path+strfile
            parser = None

            if filetype in CoreIRParser.get_extensions():
                parser = CoreIRParser(abstract_clock, symbolic_init, no_clock)
                parser.boolean = boolean
                parser.deterministic = deterministic
                self.parser = parser

            if filetype in ExplicitTSParser.get_extensions():
                parser = ExplicitTSParser()

                if not self.parser:
                    self.parser = parser
                                        
            if filetype in SymbolicTSParser.get_extensions():
                parser = SymbolicTSParser()

                if not self.parser:
                    self.parser = parser

            if filetype in SymbolicSimpleTSParser.get_extensions():
                parser = SymbolicSimpleTSParser()

                if not self.parser:
                    self.parser = parser
                    
            if filetype in BTOR2Parser.get_extensions():
                parser = BTOR2Parser()

                if not self.parser:
                    self.parser = parser
                    
            if parser is not None:
                if not os.path.isfile(strfile):
                    Logger.error("File \"%s\" does not exist"%strfile)

                Logger.msg("Parsing file \"%s\"... "%(strfile), 0)
                (hts_a, inv_a, ltl_a) = parser.parse_file(strfile, flags)
                hts.combine(hts_a)

                invar_props += inv_a
                ltl_props += ltl_a
                
                Logger.log("DONE", 0)
                continue

            Logger.error("Filetype \"%s\" unsupported"%filetype)

        if Logger.level(1):
            print(hts.print_statistics(name, Logger.level(2)))

        return (hts, invar_props, ltl_props)

    def solve_problems(self, problems, config):
        if len(problems.problems) == 0:
            Logger.error("No problems defined")
            
        if VerificationType.LTL in [problem.verification for problem in problems.problems]:
            ltl_reset_env()
        
        # generate systems for each problem configuration
        systems = {}
        for si in problems.symbolic_inits:
            (systems[('hts', si)], _, _) = self.parse_model(problems.relative_path, problems.model_file, problems.abstract_clock, si, "System 1", boolean=problems.boolean, no_clock=problems.no_clock)

        if problems.equivalence is not None:
            (systems[('hts2', si)], _, _) = self.parse_model(problems.relative_path, problems.equivalence, problems.abstract_clock, si, "System 2", boolean=problems.boolean, no_clock=problems.no_clock)
        else:
            systems[('hts2', si)] = None

        for problem in problems.problems:
            problem.hts = systems[('hts', problem.symbolic_init)]
            problem.hts2 = systems[('hts2', problem.symbolic_init)]
            problem.abstract_clock = problems.abstract_clock
            problem.no_clock = problems.no_clock
            problem.relative_path = problems.relative_path

            if config.time or problems.time:
                timer_solve = Logger.start_timer("Problem %s"%problem.name, False)
            try:
                self.solve_problem(problem, config)
                Logger.msg(" %s\n"%problem.status, 0, not(Logger.level(1)))
                
                if config.time or problems.time:
                    problem.time = Logger.get_timer(timer_solve, False)
                
            except KeyboardInterrupt as e:
                Logger.msg("\b\b Skipped!\n", 0)

    def problem2mc_config(self, problem, config):
        mc_config = MCConfig()

        config_selection = lambda problem, config: config if problem is None else problem
        
        mc_config.smt2file = config_selection(problem.smt2_tracing, config.smt2file)
        mc_config.full_trace = problem.full_trace or config.full_trace
        mc_config.trace_vars_change = problem.trace_vars_change or config.trace_vars_change
        mc_config.trace_all_vars = problem.trace_all_vars or config.trace_all_vars
        mc_config.prefix = problem.name
        mc_config.strategy = config_selection(problem.strategy, config.strategy)
        mc_config.incremental = config_selection(problem.incremental, config.incremental)
        mc_config.skip_solving = config_selection(problem.skip_solving, config.skip_solving)
        mc_config.map_function = self.parser.remap_an2or
        mc_config.solver_name = config_selection(problem.solver_name, config.solver_name)
        mc_config.vcd_trace = problem.vcd or config.vcd
        mc_config.prove = config_selection(problem.prove, config.prove)
        mc_config.properties = problem.formula
        mc_config.assumptions = problem.assumptions
        mc_config.lemmas = problem.lemmas

        return mc_config
