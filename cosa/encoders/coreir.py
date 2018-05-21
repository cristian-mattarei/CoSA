# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import coreir
import sys

from six.moves import cStringIO

from pysmt.shortcuts import Symbol, BV, TRUE, FALSE, And, EqualsOrIff, BVExtract
from pysmt.typing import BOOL, _BVType
from pysmt.smtlib.printers import SmtPrinter

from cosa.transition_systems import TS, HTS, L_BV, L_ABV
from cosa.utils.generic import is_number, status_bar
from cosa.utils.logger import Logger
from cosa.encoders.model import ModelParser, ModelFlags
from cosa.encoders.modules import Modules, SEP, CSEP

CR = "_const_replacement"
RCR = "_reg_const_replacement"
SELF = "self"

class CoreIRModelFlags(ModelFlags):
    FC_LEMMAS = "FC-LEMMAS"

class CoreIRParser(ModelParser):
    extension = "json"
    
    abstract_clock = None
    symbolic_init = None

    context = None

    attrnames = None
    boolean = False
    pack_connections = False
    anonimize_names = False
    map_an2or = None
    map_or2an = None
    idvars = 0
    
    def __init__(self, abstract_clock, symbolic_init, *libs):
        self.context = coreir.Context()
        for lib in libs:
            self.context.load_library(lib)

        self.abstract_clock = abstract_clock
        self.symbolic_init = symbolic_init

        self.__init_attrnames()

        self.boolean = False
        self.pack_connections = True
        self.map_an2or = {}
        self.map_or2an = {}
        self.anonimize_names = False

        self._init_mod_map()

        self.memoize_encoding = False

        self.enc_map = {}

        Logger.time = True

        
    @staticmethod        
    def get_extension():
        return CoreIRParser.extension
        
    def run_passes(self):
        self.context.run_passes(['rungenerators',\
                                 'cullgraph',\
                                 'cullzexts',\
                                 'removeconstduplicates',\
                                 'packconnections',\
                                 'clockifyinterface',
                                 'flattentypes',\
                                 'flatten',\
                                 'deletedeadinstances'])


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
            raise UndefinedTypeException("Bit Vector undefined for width = {}".format(width))

        orname = name.replace(CSEP, SEP)

        if not self.anonimize_names:
            name = orname
        else:
            name = self.__new_var_name()
            self.map_an2or[name] = orname
            self.map_or2an[orname] = name

        if self.boolean and (width == 1):
            return Symbol(name, BOOL)

        return Symbol(name, _BVType(width))

        
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
            ts = TS(set_remap(enc.vars, remap), self.subwalker.walk(enc.init), self.subwalker.walk(enc.trans), self.subwalker.walk(enc.invar))
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
    
    def parse_file(self, strfile, flags=None):
        Logger.msg("Reading CoreIR system... ", 1)
        top_module = self.context.load_from_file(strfile)

        Modules.abstract_clock = self.abstract_clock
        Modules.symbolic_init = self.symbolic_init
        
        top_def = top_module.definition
        interface = list(top_module.type.items())
        modules = {}

        not_defined_mods = []

        hts = HTS(top_module.name)

        Logger.msg("Starting encoding... ", 1)

        totalinst = len(top_def.instances)
        count = 0
        top_def_instances = list(top_def.instances)

        def extract_value(x, modname, inst_intr, inst_conf, inst_mod):
            if x in inst_intr:
                return self.BVVar(modname+x, inst_intr[x].size)

            if x in inst_conf:
                xval = inst_conf[x].value
                if type(xval) == bool:
                    xval = 1 if xval else 0
                else:
                    if type(xval) != int:
                        xval = xval.unsigned_value

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
            
            inst_name = inst.selectpath
            inst_conf = inst.config
            inst_mod  = inst.module
            inst_type = inst_mod.name
            inst_intr = dict(inst_mod.type.items())
            modname = (SEP.join(inst_name))+SEP

            values_dic = {}

            for x in self.attrnames:
                values_dic[x] = extract_value(x, modname, inst_intr, inst_conf, inst_mod)

            def args(ports_list):
                return [values_dic[x] for x in ports_list]

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

            del(values_dic)
            
        for var in interface:
            varname = SELF+SEP+var[0]
            bvvar = self.BVVar(varname, var[1].size)
            hts.add_var(bvvar)
            if(var[1].is_input()):
                hts.inputs.add(bvvar)
            else:
                hts.outputs.add(bvvar)

            # Adding clock behavior
            if (self.CLK in var[0].lower()) and (var[1].is_input()):
                Logger.log("Adding clock behavior to \"%s\" input"%(varname), 1)
                ts = Modules.Clock(bvvar)
                
                if (flags is not None) and (CoreIRModelFlags.NO_INIT in flags):
                    ts.init = TRUE()
                
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

        for conn in top_def.connections:

            first_selectpath = split_paths(conn.first.selectpath)
            second_selectpath = split_paths(conn.second.selectpath)
            
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
            
            if (firstvar is None) and (secondvar is not None):
                Logger.error("Symbol \"%s\" is not defined"%firstname)
                first = (Symbol(self.remap_or2an(firstname), secondvar.symbol_type()), None)
            else:
                if (is_number(first_selectpath[-1])) and (firstvar.symbol_type() != BOOL) and (firstvar.symbol_type().width > 1):
                    sel = int(first_selectpath[-1])
                    first = (firstvar, sel) #BVExtract(first, sel, sel)

            if (firstvar is not None) and (secondvar is None):
                Logger.error("Symbol \"%s\" is not defined"%secondname)
                second = (Symbol(self.remap_or2an(secondname), firstvar.symbol_type()), None)
            else:
                if (is_number(second_selectpath[-1])) and (secondvar.symbol_type() != BOOL) and (secondvar.symbol_type().width > 1):
                    sel = int(second_selectpath[-1])
                    second = (secondvar, sel) #BVExtract(second, sel, sel)

            assert((firstvar is not None) and (secondvar is not None))

            eq_conns.append((first, second))

            eq_vars.add(firstvar)
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

        ts = TS(eq_vars, TRUE(), TRUE(), eq_formula)
        ts.comment = "Connections" # (%s, %s)"%(SEP.join(first_selectpath), SEP.join(second_selectpath))

        hts.add_ts(ts)

        if self.enc_map is not None:
            del(self.enc_map)

        if Logger.level(2):
            Logger.get_timer(ttimer)

        return hts


    def __pack_connections(self, connections):

        new_conns = []
        dict_conns = {}

        for conn in connections:
            (first, second) = (conn[0][0], conn[1][0])
            (sel1, sel2) = (conn[0][1], conn[1][1])

            if first.symbol_name() > second.symbol_name():
                (first, second, sel1, sel2) = (second, first, sel2, sel1)

            if (first, second) not in dict_conns:
                dict_conns[(first, second)] = []
            
            dict_conns[(first, second)].append((sel1, sel2))

        ex_set = 0
        tr_set = 0

        for conn in dict_conns:
            (first,second) = conn
            (tcon, conns) = self.__analyze_connections(dict_conns[conn])

            if tcon == 1:
                ex_set += 1

            if tcon == 2:
                tr_set += 1
                
            if conns is None:
                for single_conn in dict_conns[conn]:
                    new_conns.append(((first, single_conn[0]),(second, single_conn[1])))
            else:
                ((min_1, max_1), (min_2, max_2)) = conns
                new_conns.append(((first, min_1, max_1),(second, min_2, max_2)))
                
        return new_conns


    def __analyze_connections(self, indexes):
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
                return (1, ((min_1, max_1), (min_2, max_2)))

            d_min = (min_1 - min_2) if min_1 > min_2 else (min_2 - min_1)
            d_max = (max_1 - max_2) if max_1 > max_2 else (max_2 - max_1)

            # Transposed set e.g., [0,1,2,3] = [5,6,7,8]
            if (min_1 == inds_1[0]) and (min_2 == inds_2[0]) and (max_1 == inds_1[-1]) and (max_2 == inds_2[-1]) \
               and (d_min == d_max) and (len(inds_1) == len(inds_2)):
                return (2, ((min_1, max_1), (min_2, max_2)))
            
        return (-1, None)
    

    
