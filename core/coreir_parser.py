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

from pysmt.shortcuts import get_env, Symbol, BV, simplify, \
    TRUE, FALSE, \
    And, Implies, Iff, Not, BVAnd, EqualsOrIff, \
    BVExtract, BVSub, BVOr, BVAdd, BVXor, BVMul, BVNot, BVZExt, BVLShr, BVAShr, BVULT, BVUGT, BVUGE

from pysmt.typing import BOOL, _BVType
from pysmt.smtlib.printers import SmtPrinter

from core.transition_system import TS, HTS, SEP
from util.utils import is_number
from util.logger import Logger
from six.moves import cStringIO

SELF = "self"

def BVVar(name, width):
    if width <= 0 or not isinstance(width, int):
        raise UndefinedTypeException("Bit Vector undefined for width = {}".format(width))

    return Symbol(name, _BVType(width))

class Modules(object):

    @staticmethod
    def Uop(op, in_, out):
        # INVAR: (<op> in) = out)
        vars_ = [in_,out]
        comment = (";; " + op.__name__ + " (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        invar = EqualsOrIff(op(in_), out)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Not(in_,out):
        return Modules.Uop(BVNot,in_,out)
    
    @staticmethod
    def Bop(op, in0, in1, out):
        # INVAR: (in0 <op> in1) = out
        vars_ = [in0,in1,out]
        comment = (";; " + op.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        invar = EqualsOrIff(op(in0,in1), out)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def BopBool(op, in0, in1, out):
        # INVAR: (in0 <op> in1) = out
        vars_ = [in0,in1,out]
        comment = (";; " + op.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        bout = EqualsOrIff(out, BV(1, 1))
        invar = Iff(op(in0,in1), bout)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    @staticmethod
    def LShr(in0,in1,out):
        return Modules.Bop(BVLShr,in0,in1,out)

    @staticmethod
    def AShr(in0,in1,out):
        return Modules.Bop(BVAShr,in0,in1,out)

    @staticmethod
    def Add(in0,in1,out):
        return Modules.Bop(BVAdd,in0,in1,out)

    @staticmethod
    def And(in0,in1,out):
        return Modules.Bop(BVAnd,in0,in1,out)

    @staticmethod
    def Xor(in0,in1,out):
        return Modules.Bop(BVXor,in0,in1,out)
    
    @staticmethod
    def Or(in0,in1,out):
        return Modules.Bop(BVOr,in0,in1,out)
    
    @staticmethod
    def Sub(in0,in1,out):
        return Modules.Bop(BVSub,in0,in1,out)

    @staticmethod
    def Mul(in0,in1,out):
        return Modules.Bop(BVMul,in0,in1,out)

    @staticmethod
    def Ult(in0,in1,out):
        return Modules.BopBool(BVULT,in0,in1,out)
    
    @staticmethod
    def Ule(in0,in1,out):
        return Modules.Bop(BVUle,in0,in1,out)
    
    @staticmethod
    def Ugt(in0,in1,out):
        return Modules.BopBool(BVUGT,in0,in1,out)
    
    @staticmethod
    def Uge(in0,in1,out):
        return Modules.BopBool(BVUGE,in0,in1,out)
    
    @staticmethod
    def Slt(in0,in1,out):
        return Modules.Bop(BVSlt,in0,in1,out)
    
    @staticmethod
    def Sle(in0,in1,out):
        return Modules.Bop(BVSle,in0,in1,out)
    
    @staticmethod
    def Sgt(in0,in1,out):
        return Modules.Bop(BVSgt,in0,in1,out)
    
    @staticmethod
    def Sge(in0,in1,out):
        return Modules.Bop(BVSge,in0,in1,out)

    @staticmethod
    def Zext(in_,out):
        # INVAR: (<op> in) = out)
        vars_ = [in_,out]
        comment = (";; ZExt (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        length = (out.symbol_type().width)-(in_.symbol_type().width)
        invar = EqualsOrIff(BVZExt(in_, length), out)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    @staticmethod
    def Const(out, value):
        const = BV(value, out.symbol_type().width)
        formula = EqualsOrIff(out, const)
        comment = ";; Const (out, val) = (" + out.symbol_name() + ", " + str(const) + ")"
        Logger.log(comment, 1)
        ts = TS(set([out]), TRUE(), TRUE(), formula)
        ts.comment = comment
        return ts

    @staticmethod
    def Clock(clk):
        # INIT: clk = 0
        # TRANS: clk' = !clk
        bclk = EqualsOrIff(clk, BV(1, 1))
        init = Not(bclk)
        trans = EqualsOrIff(Not(bclk), TS.to_next(bclk))
        ts = TS(set([clk]), init, trans, TRUE())
        ts.comment = ""
        return ts

    @staticmethod
    def Reg(in_, clk, clr, rst, out, initval):
        # INIT: out = initval
        # TRANS: ((!clk & clk') -> (((clr) -> (out' = 0)) & ((rst & !clr) -> (out' = initval)) & ((!rst & !clr) -> (out' = in)))) & 
        #        (!(!clk & clk') -> (out' = out)))
        # trans gives priority to clr signal over rst
        vars_ = [in_,clk,clr,rst,out]
        comment = ";; Reg (in, clk, clr, rst, out) = (%s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 1)
        binitval = BV(initval, out.symbol_type().width)
        init = EqualsOrIff(out, binitval)
        if clr is not None:
            bclr = EqualsOrIff(clr, BV(1, 1))
        else:
            bclr = FALSE()

        if rst is not None:
            brst = EqualsOrIff(rst, BV(1, 1))
        else:
            brst = FALSE()
            
        bclk = EqualsOrIff(clk, BV(1, 1))
        zero = BV(0, out.symbol_type().width)

        ri_clk = And(Not(bclk), TS.to_next(bclk))
        do_clk = And(bclk, Not(TS.to_next(bclk)))

        tr_clr = Implies(bclr, EqualsOrIff(TS.get_prime(out), zero))
        tr_rst_nclr = Implies(And(brst, Not(bclr)), EqualsOrIff(TS.get_prime(out), binitval))
        tr_nrst_nclr = Implies(And(Not(brst), Not(bclr)), EqualsOrIff(TS.get_prime(out), in_))
        trans_ri = And(tr_clr, tr_rst_nclr, tr_nrst_nclr)
        trans_do = EqualsOrIff(out, TS.get_prime(out))
                
        trans = And(Implies(ri_clk, trans_ri), Implies(do_clk, trans_do))
        ts = TS(set([v for v in vars_ if v is not None]), init, trans, TRUE())
        ts.state_vars = set([out])
        ts.comment = comment
        return ts

    @staticmethod
    def Mux(in0, in1, sel, out):
        # INVAR: ((sel = 0) -> (out = in0)) & ((sel = 1) -> (out = in1))
        vars_ = [in0,in1,sel,out]
        comment = ";; Mux (in0, in1, sel, out) = (%s, %s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        bsel = EqualsOrIff(sel, BV(0, 1))
        invar = And(Implies(bsel, EqualsOrIff(in0, out)), Implies(Not(bsel), EqualsOrIff(in1, out)))
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Eq(in0, in1, out):
        # INVAR: (((in0 = in1) -> (out = #b1)) & ((in0 != in1) -> (out = #b0)))
        vars_ = [in0,in1,out]
        comment = ";; Eq (in0, in1, out) = (%s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        eq = EqualsOrIff(in0, in1)
        zero = EqualsOrIff(out, BV(0, 1))
        one = EqualsOrIff(out, BV(1, 1))
        invar = And(Implies(eq, one), Implies(Not(eq), zero))
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Orr(in_, out):
        # INVAR: (in = 0) -> (out = 0) & (in != 0) -> (out = 1)
        vars_ = [in_, out]
        comment = ";; Orr (in, out) = (%s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        true_res = Implies(EqualsOrIff(in_, BV(0,in_.symbol_type().width)), EqualsOrIff(out, BV(0,1)))
        false_res = Implies(Not(EqualsOrIff(in_, BV(0,in_.symbol_type().width))), EqualsOrIff(out, BV(1,1)))
        invar = And(true_res, false_res)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Andr(in_, out):
        # INVAR: (in = 1) -> (out = 1) & (in != 1) -> (out = 0)
        vars_ = [in_, out]
        comment = ";; Andr (in, out) = (%s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 1)
        true_res = Implies(EqualsOrIff(in_, BV(1,in_.symbol_type().width)), EqualsOrIff(out, BV(1,1)))
        false_res = Implies(Not(EqualsOrIff(in_, BV(1,in_.symbol_type().width))), EqualsOrIff(out, BV(0,1)))
        invar = And(true_res, false_res)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Slice(in_, out, low, high):
        # INVAR: (extract low high in) = out
        high -= 1
        vars_ = [in_,out, low, high]
        comment = ";; Mux (in, out, low, high) = (%s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 1)
        invar = EqualsOrIff(BVExtract(in_, low, high), out)
        ts = TS(set([in_, out]), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    
class CoreIRParser(object):

    file = None
    context = None

    attrnames = None

    def __init__(self, file, *libs):
        self.context = coreir.Context()
        for lib in libs:
            self.context.load_library(lib)

        self.file = file

        self.__init_attrnames()

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
        self.attrnames.append(add_name("in"))
        self.attrnames.append(add_name("sel"))
        self.attrnames.append(add_name("value"))
        self.attrnames.append(add_name("init"))
        self.attrnames.append(add_name("low", "lo"))
        self.attrnames.append(add_name("high", "hi"))
            
    def __mod_to_impl(self, inst_type, args):
        mod_map = []
        mod_map.append(("not",  (Modules.Not,  [self.IN, self.OUT])))
        mod_map.append(("not",  (Modules.Not,  [self.IN, self.OUT])))
        mod_map.append(("zext", (Modules.Zext, [self.IN, self.OUT])))
        mod_map.append(("orr",  (Modules.Orr,  [self.IN, self.OUT])))
        mod_map.append(("andr", (Modules.Andr, [self.IN, self.OUT])))
        
        mod_map.append(("lshr", (Modules.LShr, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ashr", (Modules.AShr, [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("add",  (Modules.Add,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("and",  (Modules.And,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("xor",  (Modules.Xor,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("or",   (Modules.Or,   [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sub",  (Modules.Sub,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("mul",  (Modules.Mul,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("eq",   (Modules.Eq,   [self.IN0, self.IN1, self.OUT])))

        mod_map.append(("ult",  (Modules.Ult,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ule",  (Modules.Ule,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ugt",  (Modules.Ugt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("uge",  (Modules.Uge,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("slt",  (Modules.Slt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sle",  (Modules.Sle,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sgt",  (Modules.Sgt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sge",  (Modules.Sge,  [self.IN0, self.IN1, self.OUT])))
        
        mod_map.append(("const", (Modules.Const, [self.OUT, self.VALUE])))
        mod_map.append(("reg",   (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.OUT, self.INIT])))
        mod_map.append(("regrst",   (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.OUT, self.INIT])))
        mod_map.append(("mux",   (Modules.Mux, [self.IN0, self.IN1, self.SEL, self.OUT])))
        mod_map.append(("slice", (Modules.Slice, [self.IN, self.OUT, self.LOW, self.HIGH])))
        
        mod_map = dict(mod_map)

        ts = None
        
        if inst_type in mod_map:
            ts = mod_map[inst_type][0](*args(mod_map[inst_type][1]))

        return ts
        
    def parse(self):
        top_module = self.context.load_from_file(self.file)
        top_def = top_module.definition
        interface = list(top_module.type.items())
        modules = {}

        hts = HTS(top_module.name)
        
        for inst in top_def.instances:
            ts = None
            
            inst_name = inst.selectpath
            inst_type = inst.module.name
            inst_intr = dict(inst.module.type.items())
            modname = (SEP.join(inst_name))+SEP

            values_dic = {}

            for x in self.attrnames:
                if x in inst_intr:
                    values_dic[x] = BVVar(modname+x, inst_intr[x].size)
                else:
                    values_dic[x] = None

            for x in self.attrnames:
                if x in inst.config:
                    xval = inst.config[x].value
                    if type(xval) == bool:
                        xval = 1 if xval else 0
                    else:
                        xval = xval.val

                    values_dic[x] = xval

            if inst.module.generated:
                inst_args = inst.module.generator_args

                for x in self.attrnames:
                    if x in inst_args:
                        values_dic[x] = inst_args[x].value


            def args(ports_list):
                return [values_dic[x] for x in ports_list]

            ts = self.__mod_to_impl(inst_type, args)
                
            if ts is not None:
                hts.add_ts(ts)
            else:                
                Logger.error("Module type \"%s\" is not defined"%(inst_type))
                
        for var in interface:
            varname = SELF+SEP+var[0]
            bvvar = BVVar(varname, var[1].size)
            hts.add_var(bvvar)
            if(var[1].is_input()):
                hts.inputs.add(bvvar)
            else:
                hts.outputs.add(bvvar)

            # Adding clock behavior
            if var[0].lower() == self.CLK:
                hts.add_ts(Modules.Clock(bvvar))

        varmap = dict([(s.symbol_name(), s) for s in hts.vars])

        for conn in top_def.connections:
            first = SEP.join(conn.first.selectpath)
            second = SEP.join(conn.second.selectpath)

            if is_number(conn.first.selectpath[-1]):
                first = varmap[SEP.join(conn.first.selectpath[:-1])]
                sel = int(conn.first.selectpath[-1])
                first = BVExtract(first, sel, sel)
            else:
                first = varmap[SEP.join(conn.first.selectpath)]

            if is_number(conn.second.selectpath[-1]):
                second = varmap[SEP.join(conn.second.selectpath[:-1])]
                sel = int(conn.second.selectpath[-1])
                second = BVExtract(second, sel, sel)
            else:
                second = varmap[SEP.join(conn.second.selectpath)]
                
            eq = EqualsOrIff(first, second)

            Logger.log(str(eq), 1)

            hts.add_ts(TS(set([]), TRUE(), TRUE(), eq))

        return hts
