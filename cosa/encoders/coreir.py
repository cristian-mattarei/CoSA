# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

COREIR = True

try:
    import coreir
except:
    COREIR = False

from six.moves import cStringIO

from pysmt.shortcuts import Symbol, BV, TRUE, FALSE, And, EqualsOrIff, BVExtract, BVConcat, Ite
from pysmt.typing import BOOL, BVType
from pysmt.smtlib.printers import SmtPrinter

from cosa.representation import TS, HTS, L_BV, L_ABV
from cosa.utils.generic import is_number, status_bar
from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser, ModelFlags, ModelInformation
from cosa.encoders.modules import Modules, ModuleSymbols, SEP, CSEP
from cosa.printers.template import HIDDEN_VAR
from cosa.utils.generic import bin_to_dec, suppress_output, restore_output

CR = "_const_replacement"
RCR = "_reg_const_replacement"
SELF = "self"
NAMED = 'Named'
COREIR_CLK = 'coreir.clkIn'

LIBRARIES = []
LIBRARIES.append("rtlil")

PASSES = []
PASSES.append("clockifyinterface")
#PASSES.append("wireclocks")
#PASSES.append("coreir")
PASSES.append("rungenerators")
PASSES.append("removeconstduplicates")
PASSES.append("deletedeadinstances")
PASSES.append("rungenerators")
PASSES.append("cullgraph")
PASSES.append("removebulkconnections")
#PASSES.append("removepassthroughs")
PASSES.append("removeunconnected")
#PASSES.append("fold")
#PASSES.append("constants")
PASSES.append("flatten")
PASSES.append("flattentypes")
PASSES.append("packconnections")
PASSES.append("cullzexts")

class CoreIRModelFlags(ModelFlags):
    FC_LEMMAS = "FC-LEMMAS"

class CoreIRParser(ModelParser):
    extensions = ["json"]
    name = "CoreIR"

    context = None

    attrnames = None
    pack_connections = False
    anonimize_names = False
    map_an2or = None
    map_or2an = None
    bitvec_new_version = True
    idvars = 0
    enc_map = None
    abstract_clock_list = None
    clock_list = None

    enabled = True

    def is_available(self):
        return COREIR

    def __init__(self):
        if COREIR:
            self.context = coreir.Context()
            for lib in LIBRARIES:
                self.context.load_library(lib)

            self.__init_attrnames()

            self.pack_connections = True
            self.anonimize_names = False

            self.memoize_encoding = False

            self.__reset_structures()

            Logger.time = True

    def __reset_structures(self):
        self._init_mod_map()
        self._init_sym_map()
        self.clock_list = set([])
        self.abstract_clock_list = set([])
        self.enc_map = {}
        self.map_an2or = {}
        self.map_or2an = {}

    @staticmethod
    def get_extensions():
        return CoreIRParser.extensions

    def get_model_info(self):
        model_info = ModelInformation()
        model_info.abstract_clock_list = list(self.abstract_clock_list)
        model_info.clock_list = list(self.clock_list)
        return model_info

    def run_passes(self):
        Logger.log("Running CoreIR passes...", 1)
        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()

        self.context.run_passes(PASSES)

        if not Logger.level(print_level):
            restore_output(saved_stdout)

    def __new_var_name(self):
        CoreIRParser.idvars += 1
        return "v%s"%CoreIRParser.idvars

    def remap_an2or(self, name):
        if not self.anonimize_names:
            return name
        if name in self.map_an2or:
            return self.map_an2or[name]
        return name

    def remap_or2an(self, name):
        if not self.anonimize_names:
            return name
        if name in self.map_or2an:
            return self.map_or2an[name]
        return name

    def BVVar(self, name, width):
        if width <= 0 or not isinstance(width, int):
            Logger.error("Bit Vector undefined for width = {}".format(width))

        orname = name.replace(CSEP, SEP)

        if not self.anonimize_names:
            name = orname
        else:
            name = self.__new_var_name()
            self.map_an2or[name] = orname
            self.map_or2an[orname] = name

        if self.config.boolean and (width == 1):
            return Symbol(name, BOOL)

        return Symbol(name, BVType(width))


    def __init_attrnames(self):
        def add_name(name, varname=None):
            if varname is None:
                varname = name

            setattr(self, name.upper(), varname)
            return varname

        self.attrnames = []
        self.attrnames.append(add_name("in0"))
        self.attrnames.append(add_name("in1"))
        self.attrnames.append(add_name("out"))
        self.attrnames.append(add_name("clk"))
        self.attrnames.append(add_name("clr"))
        self.attrnames.append(add_name("rst"))
        self.attrnames.append(add_name("arst"))
        self.attrnames.append(add_name("clk_posedge"))
        self.attrnames.append(add_name("arst_posedge"))
        self.attrnames.append(add_name("in"))
        self.attrnames.append(add_name("sel"))
        self.attrnames.append(add_name("value"))
        self.attrnames.append(add_name("init"))
        self.attrnames.append(add_name("low", "lo"))
        self.attrnames.append(add_name("high", "hi"))

        # memory interface
        self.attrnames.append(add_name("wdata"))
        self.attrnames.append(add_name("waddr"))
        self.attrnames.append(add_name("wen"))
        self.attrnames.append(add_name("rdata"))
        self.attrnames.append(add_name("raddr"))


    def _init_mod_map(self):
        mod_map = []
        mod_map.append(("not",  (Modules.Not,  [self.IN, self.OUT])))
        mod_map.append(("not",  (Modules.Not,  [self.IN, self.OUT])))
        mod_map.append(("zext", (Modules.Zext, [self.IN, self.OUT])))
        mod_map.append(("orr",  (Modules.Orr,  [self.IN, self.OUT])))
        mod_map.append(("andr", (Modules.Andr, [self.IN, self.OUT])))
        mod_map.append(("wrap", (Modules.Wrap, [self.IN, self.OUT])))

        mod_map.append(("shl",  (Modules.LShl, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("lshl", (Modules.LShl, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("lshr", (Modules.LShr, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ashr", (Modules.AShr, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("add",  (Modules.Add,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("and",  (Modules.And,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("xor",  (Modules.Xor,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("or",   (Modules.Or,   [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sub",  (Modules.Sub,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("mul",  (Modules.Mul,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("udiv",  (Modules.Udiv,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sdiv",  (Modules.Sdiv,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("eq",   (Modules.Eq,   [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("neq",  (Modules.Neq,  [self.IN0, self.IN1, self.OUT])))

        mod_map.append(("ult",  (Modules.Ult,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ule",  (Modules.Ule,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ugt",  (Modules.Ugt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("uge",  (Modules.Uge,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("slt",  (Modules.Slt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sle",  (Modules.Sle,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sgt",  (Modules.Sgt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sge",  (Modules.Sge,  [self.IN0, self.IN1, self.OUT])))

        mod_map.append(("const",  (Modules.Const, [self.OUT, self.VALUE])))
        mod_map.append(("reg",    (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.ARST, self.OUT, self.INIT, self.CLK_POSEDGE, self.ARST_POSEDGE])))
        mod_map.append(("mem", (Modules.Mem, [self.CLK, self.WDATA, self.WADDR, self.WEN, self.RDATA, self.RADDR])))
        mod_map.append(("regrst", (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.ARST, self.OUT, self.INIT, self.CLK_POSEDGE, self.ARST_POSEDGE])))
        mod_map.append(("reg_arst", (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.ARST, self.OUT, self.INIT, self.CLK_POSEDGE, self.ARST_POSEDGE])))
        mod_map.append(("mux",    (Modules.Mux, [self.IN0, self.IN1, self.SEL, self.OUT])))
        mod_map.append(("slice",  (Modules.Slice, [self.IN, self.OUT, self.LOW, self.HIGH])))
        mod_map.append(("concat", (Modules.Concat, [self.IN0, self.IN1, self.OUT])))

        mod_map.append(('term', (Modules.Term, [self.IN])))

        self.mod_map = dict(mod_map)

    def _init_sym_map(self):
        sym_map = []

        sym_map.append(("const",  (ModuleSymbols.Const, [self.OUT, self.VALUE])))

        self.sym_map = dict(sym_map)

    def __encoding_memoization(self, inst_type, args):
        value = 0
        vec_par = []
        actual = []
        for x in args:
            if x is not None:
                if type(x) != int:
                    value += 1
                    vec_par.append(("a%s"%value, x.symbol_type().width))
                    actual.append(x)
            else:
                vec_par.append(x)


        def join(l1, l2):
            ret = []
            for i in range(len(l1)):
                ret.append((l1[i], l2[i]))

            return ret

        def set_remap(in_set, remap):
            ret = set([])

            source = False

            for v in in_set:
                if v in remap:
                    ret.add(remap[v])
                else:
                    if source is False:
                        base_source = ".".join(list(in_set)[0].symbol_name().split(".")[:-1])
                        base_dest = ".".join(remap[list(in_set)[0]].symbol_name().split(".")[:-1])
                        source = True

                    ret.add(Symbol(v.symbol_name().replace(base_source, base_dest), v.symbol_type()))

            return ret

        enc_val = (inst_type, str(vec_par))
        if enc_val in self.enc_map:
            (enc, formal) = self.enc_map[enc_val]
            remap = dict(join(formal, actual))
            self.subwalker.set_substitute_map(remap)
            ts = TS()
            ts.vars = set_remap(enc.vars, remap)
            ts.set_behavior(self.subwalker.walk(enc.init), self.subwalker.walk(enc.trans), self.subwalker.walk(enc.invar))
            return ts

        ret = self.mod_map[inst_type][0](*args)
        self.enc_map[enc_val] = (ret, actual)

        return ret

    def __mod_to_impl(self, inst_type, args):
        ts = None

        if inst_type in self.mod_map:
            if self.memoize_encoding:
                ts = self.__encoding_memoization(inst_type, args(self.mod_map[inst_type][1]))
            else:
                ts = self.mod_map[inst_type][0](*args(self.mod_map[inst_type][1]))

        if ((args([self.CLK_POSEDGE])[0] == 0) or (args([self.ARST_POSEDGE])[0] == 0)) and Modules.abstract_clock:
            Logger.warning("Unsound clock abstraction: registers with negedge behavior")

        return ts

    def __mod_to_sym(self, inst_type, args):
        sym = None

        if inst_type in self.sym_map:
            if self.memoize_encoding:
                sym = self.__encoding_memoization(inst_type, args(self.sym_map[inst_type][1]))
            else:
                sym = self.sym_map[inst_type][0](*args(self.sym_map[inst_type][1]))

        return sym

    def parse_file(self, file_path, config, flags=None):
        # coreir needs a string representing the path
        strfile = str(file_path)

        self.config = config
        self.__reset_structures()

        Logger.msg("Reading CoreIR system... ", 1)
        top_module = self.context.load_from_file(strfile)

        if config.run_coreir_passes:
            self.run_passes()

        Modules.abstract_clock = self.config.abstract_clock
        Modules.symbolic_init = self.config.symbolic_init

        top_def = top_module.definition
        interface = list(top_module.type.items())
        modules = {}
        sym_map = {}

        not_defined_mods = []

        hts = HTS(top_module.name)
        invar_props = []
        ltl_props = []

        Logger.msg("Starting encoding... ", 1)

        count = 0

        def extract_value(x, modname, inst_intr, inst_conf, inst_mod):
            if x in inst_intr:
                return self.BVVar(modname+x, inst_intr[x].size)

            if x in inst_conf:
                xval = inst_conf[x].value
                if type(xval) == bool:
                    xval = 1 if xval else 0
                else:
                    if type(xval) != int:
                        try:
                            xval = xval.as_uint()
                        except:
                            xval = None
                return xval

            if inst_mod.generated:
                inst_args = inst_mod.generator_args
                if x in inst_args:
                    return inst_args[x].value

            return None

        if Logger.level(1):
            timer = Logger.start_timer("IntConvertion", False)
            en_tprinting = False

        if Logger.level(2):
            ttimer = Logger.start_timer("Convertion", False)

        td_instances = top_def.instances
        top_def_instances = [(inst.selectpath, inst.config, inst.module) for inst in td_instances]
        # sorting keeps the behavior deterministic
        top_def_instances.sort()

        totalinst = len(top_def_instances)

        for inst in top_def_instances:
            if Logger.level(1):
                count += 1
                if count % 300 == 0:
                    dtime = Logger.get_timer(timer, False)
                    if dtime > 2:
                        en_tprinting = True
                    if en_tprinting:
                        Logger.inline("%s"%status_bar((float(count)/float(totalinst))), 1)
                        timer = Logger.start_timer("IntConvertion", False)

                    if Logger.level(2):
                        Logger.get_timer(timer, False)

            ts = None

            (inst_name, inst_conf, inst_mod) = inst
            inst_type = inst_mod.name
            inst_intr = dict(inst_mod.type.items())
            modname = (SEP.join(inst_name))+SEP

            values_dic = {}

            for x in self.attrnames:
                values_dic[x] = extract_value(x, modname, inst_intr, inst_conf, inst_mod)

            def args(ports_list):
                return [values_dic[x] for x in ports_list]

            sym = self.__mod_to_sym(inst_type, args)
            if sym is not None:
                sym_map[sym[0].symbol_name()] = (sym[0], sym[1])
                continue

            ts = self.__mod_to_impl(inst_type, args)

            if ts is not None:

                if flags is not None:
                    if CoreIRModelFlags.NO_INIT in flags:
                        ts.init = TRUE()

                    if CoreIRModelFlags.FC_LEMMAS in flags:
                        for v in ts.vars:
                            v_name = v.symbol_name()
                            if (CR in v_name) or (RCR in v_name):
                                cons_v_name = v_name[:len(CR)] if CR in v_name else v_name[:len(RCR)]
                                cons_v = Symbol(cons_v_name, v.symbol_type())
                                lemma = EqualsOrIff(cons_v, BV(values_dic[self.VALUE], cons_v.symbol_type().width))
                                hts.add_lemma(lemma)

                        for v in ts.state_vars:
                            lemma = EqualsOrIff(v, BV(values_dic[self.INIT], v.symbol_type().width))
                            hts.add_lemma(lemma)

                hts.add_ts(ts)
            else:
                if inst_type not in not_defined_mods:
                    intface = ", ".join(["%s"%(v) for v in values_dic if values_dic[v] is not None])
                    Logger.error("Module type \"%s\" with interface \"%s\" is not defined"%(inst_type, intface))
                    not_defined_mods.append(inst_type)

        Logger.clear_inline(1)

        # sorting keeps the behavior deterministic
        interface.sort()

        for var in interface:
            varname = SELF+SEP+var[0]
            bvvar = self.BVVar(varname, var[1].size)
            if(var[1].is_input()):
                hts.add_input_var(bvvar)
            else:
                hts.add_output_var(bvvar)

            if var[1].kind == NAMED and var[1].name == COREIR_CLK:
                self.clock_list.add(bvvar)
                if self.config.abstract_clock:
                    self.abstract_clock_list.add((bvvar, (BV(0, var[1].size), BV(1, var[1].size))))
                else:
                    # add state variable that stores the previous clock value
                    # This is IMPORTANT for model checking soundness, but
                    #    it isn't obvious that this is necessary
                    #
                    # imagine we have an explicit clock encoding (not abstract_clock), e.g.
                    #   next(state_var) = (!clk & next(clk)) ? <state_update> : <old value>
                    # and if we're trying to prove something using k-induction, there's a "loop free"
                    #   constraint that the state and output variables don't repeat (reach the same
                    #   state twice) in the trace
                    #   but on a negedge clock, there can be scenarios where no state or outputs
                    #   can be updated and we'll get a trivial unsat which will be interpreted as
                    #   a converged proof -- uh oh
                    #
                    # adding this state element just ensures that the loop free constraint won't
                    #   be violated trivially
                    # e.g. on a neg-edge clock, this new state element will have changed

                    # make it hidden (won't be printed)
                    # HIDDEN_VAR is a prefix that printers check for
                    trailing_clock_var = self.BVVar("{}{}__prev".format(HIDDEN_VAR, varname), var[1].size)

                    ts = TS()
                    ts.add_state_var(trailing_clock_var)
                    # the initial state for this trailing variable is unconstrained
                    ts.set_behavior(TRUE(), EqualsOrIff(TS.get_prime(trailing_clock_var), bvvar), TRUE())

                    hts.add_ts(ts)

        varmap = dict([(s.symbol_name(), s) for s in hts.vars])

        def split_paths(path):
            ret = []
            for el in path:
                ret += el.split(CSEP)

            return ret

        def dict_select(dic, el):
            return dic[el] if el in dic else None

        eq_conns = []
        eq_vars = set([])

        td_connections = top_def.connections
        top_def_connections = [((conn.first.selectpath, conn.second.selectpath) if conn.first.selectpath < conn.second.selectpath else (conn.second.selectpath, conn.first.selectpath), conn) for conn in td_connections]
        # sorting keeps the behavior deterministic
        top_def_connections.sort()

        for conn in top_def_connections:

            first_selectpath = split_paths(conn[0][0])
            second_selectpath = split_paths(conn[0][1])

            first = SEP.join(first_selectpath)
            second = SEP.join(second_selectpath)

            firstvar = None
            secondvar = None

            if is_number(first_selectpath[-1]):
                firstname = SEP.join(first_selectpath[:-1])
            else:
                firstname = SEP.join(first_selectpath)

            if is_number(second_selectpath[-1]):
                secondname = SEP.join(second_selectpath[:-1])
            else:
                secondname = SEP.join(second_selectpath)

            first = (dict_select(varmap, self.remap_or2an(firstname)), None)
            second = (dict_select(varmap, self.remap_or2an(secondname)), None)

            firstvar = first[0]
            secondvar = second[0]

            if (firstvar is None) and (self.remap_or2an(firstname) in sym_map):
                firstvar = sym_map[self.remap_or2an(firstname)][1]

            if (secondvar is None) and (self.remap_or2an(secondname) in sym_map):
                secondvar = sym_map[self.remap_or2an(secondname)][1]

            if (firstvar is None) and (secondvar is not None):
                Logger.error("Symbol \"%s\" is not defined"%firstname)
                first = (Symbol(self.remap_or2an(firstname), secondvar.symbol_type()), None)
            else:
                if firstvar.is_constant():
                    sel = int(first_selectpath[-1]) if (is_number(first_selectpath[-1])) else None
                    first = (firstvar, sel)
                else:
                    if (is_number(first_selectpath[-1])) and (firstvar.symbol_type() != BOOL) and (firstvar.symbol_type().width > 1):
                        sel = int(first_selectpath[-1])
                        first = (firstvar, sel)

            if (firstvar is not None) and (secondvar is None):
                Logger.error("Symbol \"%s\" is not defined"%secondname)
                second = (Symbol(self.remap_or2an(secondname), firstvar.symbol_type()), None)
            else:
                if secondvar.is_constant():
                    sel = int(second_selectpath[-1]) if (is_number(second_selectpath[-1])) else None
                    second = (secondvar, sel)
                else:
                    if (is_number(second_selectpath[-1])) and (secondvar.symbol_type() != BOOL) and (secondvar.symbol_type().width > 1):
                        sel = int(second_selectpath[-1])
                        second = (secondvar, sel)

            assert((firstvar is not None) and (secondvar is not None))

            eq_conns.append((first, second))

            if firstvar.is_symbol():
                eq_vars.add(firstvar)
            if secondvar.is_symbol():
                eq_vars.add(secondvar)

        conns_len = len(eq_conns)

        if self.pack_connections:
            eq_conns = self.__pack_connections(eq_conns)

        if len(eq_conns) < conns_len:
            Logger.log("Packed %d connections"%(conns_len - len(eq_conns)), 1)


        eq_formula = TRUE()

        for eq_conn in eq_conns:

            (fst, snd) = eq_conn

            if fst[1] is None:
                first = fst[0]
            else:
                if len(fst) > 2:
                    first = BVExtract(fst[0], fst[1], fst[2])
                else:
                    first = BVExtract(fst[0], fst[1], fst[1])

            if snd[1] is None:
                second = snd[0]
            else:
                if len(snd) > 2:
                    second = BVExtract(snd[0], snd[1], snd[2])
                else:
                    second = BVExtract(snd[0], snd[1], snd[1])

            if (first.get_type() != BOOL) and (second.get_type() == BOOL):
                second = Ite(second, BV(1,1), BV(0,1))

            if (first.get_type() == BOOL) and (second.get_type() != BOOL):
                first = Ite(first, BV(1,1), BV(0,1))

            eq_formula = And(eq_formula, EqualsOrIff(first, second))

            Logger.log(str(EqualsOrIff(first, second)), 3)

        ts = TS("Connections")
        ts.invar = eq_formula
        ts.vars = eq_vars

        hts.add_ts(ts)

        if self.enc_map is not None:
            del(self.enc_map)

        if Logger.level(2):
            Logger.get_timer(ttimer)

        # check that clocks were detected if there's any state
        if hts.state_vars:
            assert self.clock_list, "Expecting clocks if there are state variables"

        return (hts, invar_props, ltl_props)


    def __pack_connections(self, connections):

        new_conns = []
        dict_conns = {}

        bv0 = BV(0, 1)
        bv1 = BV(1, 1)

        for conn in connections:
            (first, second) = (conn[0][0], conn[1][0])
            (sel1, sel2) = (conn[0][1], conn[1][1])

            if first.is_constant():
                (first, second, sel1, sel2) = (second, first, sel2, sel1)

            if first.is_symbol() and second.is_symbol():
                if first.symbol_name() > second.symbol_name():
                    (first, second, sel1, sel2) = (second, first, sel2, sel1)

            if (first, second) not in dict_conns:
                dict_conns[(first, second)] = []

            dict_conns[(first, second)].append((sel1, sel2))

        for conn in dict_conns:
            (first,second) = conn

            (first, second, new_conn) = self.__analyze_connections(first, second, dict_conns[conn])

            if (new_conn is None) and (second.is_constant()):
                zeros_conn = (first, bv0)
                ones_conn = (first, bv1)

                zeros = dict_conns[zeros_conn] if zeros_conn in dict_conns else None
                ones = dict_conns[ones_conn] if ones_conn in dict_conns else None

                if (second == bv1) and (zeros is not None):
                    continue

                (first, second, new_conn) = self.__recombine_constants(first, second, zeros, ones)

            if new_conn is None:
                for single_conn in dict_conns[conn]:
                    new_conns.append(((first, single_conn[0]),(second, single_conn[1])))
            else:
                ((min_1, max_1), (min_2, max_2)) = new_conn

                symlen_1 = first.symbol_type().width if first.is_symbol() else first.bv_width()
                symlen_2 = second.symbol_type().width if second.is_symbol() else second.bv_width()

                if (max_1-min_1)+1 == symlen_1:
                    min_1 = None
                    max_1 = None

                if (max_2-min_2)+1 == symlen_2:
                    min_2 = None
                    max_2 = None

                new_conns.append(((first, min_1, max_1),(second, min_2, max_2)))

        return new_conns


    def __analyze_connections(self, first, second, indexes):
        indexes.sort()
        inds_1 = [i[0] for i in indexes if i[0] is not None]
        inds_2 = [i[1] for i in indexes if i[1] is not None]

        if (len(inds_1) > 0) and (len(inds_2) > 0):
            min_1 = min(inds_1)
            max_1 = max(inds_1)

            min_2 = min(inds_2)
            max_2 = max(inds_2)

            # Exact set e.g., [0,1,2,3] = [0,1,2,3]
            if inds_1 == inds_2:
                return (first, second, ((min_1, max_1), (min_2, max_2)))

            d_min = (min_1 - min_2) if min_1 > min_2 else (min_2 - min_1)
            d_max = (max_1 - max_2) if max_1 > max_2 else (max_2 - max_1)

            # Transposed set e.g., [0,1,2,3] = [5,6,7,8]
            if (min_1 == inds_1[0]) and (min_2 == inds_2[0]) and (max_1 == inds_1[-1]) and (max_2 == inds_2[-1]) \
               and (d_min == d_max) and (len(inds_1) == len(inds_2)):
                return (first, second, ((min_1, max_1), (min_2, max_2)))

            # Transposed and inverted set e.g., [0,1,2,3] = [8,7,6,5]
            if (min_1 == inds_1[0]) and (min_2 == inds_2[-1]) and (max_1 == inds_1[-1]) and (max_2 == inds_2[0]) \
               and (d_min == d_max) and (len(inds_1) == len(inds_2)):
                second = self.__get_reverse_encoding(second)
                return (first, second, ((min_1, max_1), (min_1, max_1)))

        return (first, second, None)

    def __get_reverse_encoding(self, bvin):
        ret = BVExtract(bvin, 0, 0)
        for i in range(bvin.symbol_type().width-1):
            ret = BVConcat(ret, BVExtract(bvin, i+1, i+1))
        return ret

    def __recombine_constants(self, first, second, zeros, ones):

        inds_z0 = []
        inds_o0 = []
        inds_z1 = []
        inds_o1 = []

        if zeros is not None:
            zeros.sort()
            inds_z0 = [i[0] for i in zeros if i[0] is not None]
            inds_z1 = [i[1] for i in zeros if i[1] is not None]
        if ones is not None:
            ones.sort()
            inds_o0 = [i[0] for i in ones if i[0] is not None]
            inds_o1 = [i[1] for i in ones if i[1] is not None]

        c_inds0 = list(set(inds_z0+inds_o0))
        c_inds1 = list(set(inds_z1+inds_o1))

        if (len(c_inds0) > 1) and (len(c_inds1) == 0):

            min_1 = min(c_inds0)
            max_1 = max(c_inds0)

            if len(c_inds0) == ((max_1 - min_1) + 1):

                inds_z = [(i, 0) for i in inds_z0]
                inds_o = [(i, 1) for i in inds_o0]
                inds = inds_z + inds_o
                inds.sort()
                inds.reverse()
                value = [str(v[1]) for v in inds]
                bvval = bin_to_dec("".join(value))

                bvlen = len(c_inds0)
                new_second = BV(bvval, bvlen)
                return (first, new_second, ((min_1, max_1),(0, bvlen-1)))


        return (first, second, None)

        # Bit Constant e.g. var[0] = 0, var[1] = 0, ...
        if (second.is_symbol()):
            return (first, second, None)

        if (len(inds_1) > 1) and (len(inds_2) == 0):

            min_1 = min(inds_1)
            max_1 = max(inds_1)

            if len(inds_1) == ((max_1 - min_1) + 1):
                val = second.constant_value()
                bvlen = len(inds_1)
                bvval = val if val == 0 else (2**bvlen)-1
                new_second = BV(bvval, bvlen)
                return (first, new_second, ((min_1, max_1),(0, bvlen-1)))

        return (first, second, None)
