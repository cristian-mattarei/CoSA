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

from cosa.utils.logger import Logger
from cosa.analyzers.mcsolver import MCConfig
from cosa.analyzers.bmc_safety import BMCSafety
from cosa.analyzers.bmc_parametric import BMCParametric
from cosa.analyzers.bmc_ltl import BMCLTL
from cosa.problem import VerificationType, Problem, VerificationStatus, Trace
from cosa.encoders.miter import Miter
from cosa.encoders.formulae import StringParser
from cosa.representation import HTS, TS
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.symbolic_transition_system import SymbolicTSParser, SymbolicSimpleTSParser
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.ltl import LTLParser
from cosa.encoders.factory import ModelParsersFactory, ClockBehaviorsFactory, GeneratorsFactory
from cosa.modifiers.factory import ModelModifiersFactory
from cosa.encoders.template import EncoderConfig, ModelInformation
from cosa.encoders.parametric_behavior import ParametricBehavior
from cosa.printers.trace import TextTracePrinter, VCDTracePrinter
from cosa.modifiers.model_extension import ModelExtension

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

        GeneratorsFactory.init_generators()
        ClockBehaviorsFactory.init_clockbehaviors()

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

    def coi(self, hts, prop):
        from pysmt.rewritings import conjunctive_partition
        from cosa.utils.formula_mngm import get_func_free_variables
        from pysmt.shortcuts import And
        from cosa.printers.factory import HTSPrintersFactory

        # hts.reset_flatten()
        # hts.flatten(cleanup=False)
        
        def intersect(min_int, set1, set2):
            count = 0
            for el in set1:
                if el in set2:
                    count += 1
                    if count >= min_int:
                        return True

            return False

        def superset(set1, set2):
            for el in set2:
                if el not in set1:
                    return False
            return True

        def depth(var):
            return var.symbol_name().split(".")
        
        coi_vars = get_func_free_variables(prop, TS.get_ref_var)

        if hts.assumptions is not None:
            for assumption in hts.assumptions:
                for v in get_func_free_variables(assumption, TS.get_ref_var):
                    coi_vars.add(v)
                    
        print(coi_vars)
        
        coits = TS("COI")
        trans = list(conjunctive_partition(hts.single_trans(rebuild=True, include_ftrans=False)))
        invar = list(conjunctive_partition(hts.single_invar(rebuild=True, include_ftrans=False)))
        init = list(conjunctive_partition(hts.single_init()))

        output_vars = hts.output_vars
        input_vars = hts.input_vars
        state_vars = hts.state_vars
        
        ftrans_dep = {}
        
        ftrans = hts.single_ftrans()
        for var, cond_assign_list in ftrans.items():
            for refvar in get_func_free_variables(var, TS.get_ref_var):
                if refvar not in ftrans_dep:
                    ftrans_dep[refvar] = []

                for cass in cond_assign_list:
                    ftrans_dep[refvar] += [x for x in get_func_free_variables(cass[0], TS.get_ref_var) if x != refvar]
                    ftrans_dep[refvar] += [x for x in get_func_free_variables(cass[1], TS.get_ref_var) if x != refvar]
                

        while True:
            coi_size = len(coi_vars)
            for f in invar+trans+init:
                fv = get_func_free_variables(f, TS.get_ref_var)
                for v in fv:
                    if v not in ftrans_dep:
                        ftrans_dep[v] = []
                    ftrans_dep[v] += [a for a in list(fv) if a != v]
                    ftrans_dep[v] = list(set(ftrans_dep[v]))

            if coi_size == len(coi_vars):
                break
                        
        # print("dep", len(ftrans_dep))
        # for var, deps in ftrans_dep.items():
        #     print(var, deps)
        #     print()
        

        all_formulas = trans+invar+init

        freevar_dic = {}

        # while True:
        #     coi_size = len(coi_vars)
        #     for f in all_formulas:
        #         if f not in freevar_dic:
        #             freevar_dic[f] = get_func_free_variables(f, TS.get_ref_var)
        #         f_fv = freevar_dic[f]
        #         if not intersect(f_fv, coi_vars):
        #             continue

        #         for v in f_fv:
        #             coi_vars.add(v)

        #     if coi_size == len(coi_vars):
        #         break
            
        #print("Vars", len(hts.vars), len(coi_vars))

        while True:
            added = False
            for v in coi_vars:
                #print("checking %s"%v)
                if v in ftrans_dep:
                    #print("adding %s"%ftrans_dep[v])

                    for dv in ftrans_dep[v]:
                        coi_vars.add(dv)
                    added = True
                    del(ftrans_dep[v])
                    break

            if not added:
                break


        trans = list(conjunctive_partition(hts.single_trans(rebuild=True, include_ftrans=True)))
        invar = list(conjunctive_partition(hts.single_invar(rebuild=True, include_ftrans=True)))

        coits.trans = [f for f in trans if intersect(2, coi_vars, get_func_free_variables(f, TS.get_ref_var))]
        coits.invar = [f for f in invar if intersect(2, coi_vars, get_func_free_variables(f, TS.get_ref_var))]
        coits.init = [f for f in init if intersect(2, coi_vars, get_func_free_variables(f, TS.get_ref_var))]

        print("Vars", len(hts.vars), len(coi_vars))
        print("Trans", len(trans), len(coits.trans))
        print("Invar", len(invar), len(coits.invar))
        print("Init", len(init), len(coits.init))

        #print(coi_vars)
        
        coits.trans = And(coits.trans)
        coits.invar = And(coits.invar)
        coits.init = And(coits.init)

        coits.vars = hts.vars#set(coi_vars)
        coits.input_vars = hts.input_vars#set([])
        coits.output_vars = hts.output_vars#set([])
        coits.state_vars = hts.state_vars#set([])

        # for var in coits.vars:
        #     if var in input_vars:
        #         coits.input_vars.add(var)
        #     if var in output_vars:
        #         coits.output_vars.add(var)
        #     if var in state_vars:
        #         coits.state_vars.add(var)

        new_hts = HTS("COI")
        new_hts.add_ts(coits)

        printer = HTSPrintersFactory.printer_by_name("STS")
        with open("/tmp/coi_model.ssts", "w") as f:
            f.write(printer.print_hts(new_hts, []))
        
        return new_hts
    
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

        problem.hts = self.coi(problem.hts, problem.formula)
            
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
            if problem.equivalence:
                (problem.hts2, _, _) = self.parse_model(problem.relative_path, \
                                                        problem.equivalence, \
                                                        encoder_config, \
                                                        "System 2")

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
        
    def parse_model(self, \
                    relative_path, \
                    model_files, \
                    encoder_config, \
                    name=None, \
                    modifier=None):
        
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

                if modifier is not None:
                    modifier(hts_a)
                 
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
        encoder_config = self.problems2encoder_config(config, problems)

        self.sparser = StringParser(encoder_config)
        self.lparser = LTLParser()

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
                                                                             modifier)
            
        if problems.equivalence is not None:
            (systems[(HTS2, si)], _, _) = self.parse_model(problems.relative_path, \
                                                           problems.equivalence, \
                                                           encoder_config, \
                                                           "System 2")
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
        encoder_config.debug = config.debug

        return encoder_config
        
