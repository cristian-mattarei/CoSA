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
import re

from six.moves import cStringIO

from pysmt.shortcuts import get_env, Symbol, BV, simplify, \
    TRUE, FALSE, \
    And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, \
    BVExtract, BVSub, BVOr, BVAdd, BVXor, BVMul, BVNot, BVZExt, BVLShr, BVLShl, BVAShr, BVULT, BVUGT, BVUGE

from pysmt.typing import BOOL, _BVType
from pysmt.smtlib.printers import SmtPrinter
from pysmt.parsing import parse

from cosa.core.transition_system import TS, HTS
from cosa.util.utils import is_number
from cosa.util.logger import Logger

SELF = "self"
INIT = "init"

KEYWORDS = ["not"]

SEP = "."
CSEP = "$"

def B2BV(var):
    return Ite(var, BV(1,1), BV(0,1))
    
def BV2B(var):
    return EqualsOrIff(var, BV(1,1))

class Modules(object):

    abstract_clock=False
    
    @staticmethod
    def Uop(bvop, bop, in_, out):
        # INVAR: (<op> in) = out)
        vars_ = [in_,out]
        comment = (bvop.__name__ + " (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)

        in_B = in_.symbol_type() == BOOL
        outB = out.symbol_type() == BOOL

        bools = (1 if in_B else 0) + (1 if outB else 0)

        if bop == None:
            if in_B:
                in_ = B2BV(in_)
            if outB:
                out = B2BV(out)
            invar = EqualsOrIff(bvop(in_), out)
        else:
            if bools == 2:
                invar = EqualsOrIff(bop(in_), out)
            elif bools == 0:
                invar = EqualsOrIff(bvop(in_), out)
            else:
                if not in_B:
                    invar = EqualsOrIff(bop(BV2B(in_)), out)
                if not outB:
                    invar = EqualsOrIff(bop(in_), BV2B(out))
                
                
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Not(in_,out):
        return Modules.Uop(BVNot,Not,in_,out)

    @staticmethod
    def Wrap(in_, out):
        # INVAR: (in = out)
        vars_ = [in_,out]
        comment = ("Wrap (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
        invar = EqualsOrIff(in_, out)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    @staticmethod
    def Bop(bvop, bop, in0, in1, out):
        # INVAR: (in0 <op> in1) = out
        vars_ = [in0,in1,out]
        comment = (bvop.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)

        in0B = in0.symbol_type() == BOOL
        in1B = in1.symbol_type() == BOOL
        outB = out.symbol_type() == BOOL

        bools = (1 if in0B else 0) + (1 if in1B else 0) + (1 if outB else 0)

        if bop == None:
            if in0B:
                in0 = Ite(in0, BV(1,1), BV(0,1))
            if in1B:
                in1 = Ite(in1, BV(1,1), BV(0,1))
            if outB:
                out = Ite(out, BV(1,1), BV(0,1))

            invar = EqualsOrIff(bvop(in0,in1), out)
        else:

            if bools == 3:
                invar = EqualsOrIff(bop(in0, in1), out)
            elif bools == 0:
                invar = EqualsOrIff(bvop(in0,in1), out)
            elif bools == 1:
                if in0B:
                    invar = EqualsOrIff(bvop(B2BV(in0),in1), out)
                if in1B:
                    invar = EqualsOrIff(bvop(in0,B2BV(in1)), out)
                if outB:
                    invar = EqualsOrIff(BV2B(bvop(in0,in1)), out)
            else:
                if not in0B:
                    invar = EqualsOrIff(bop(BV2B(in0),in1), out)
                if not in1B:
                    invar = EqualsOrIff(bop(in0,BV2B(in1)), out)
                if not outB:
                    invar = EqualsOrIff(B2BV(bop(in0, in1)), out)
                
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def BopBool(op, in0, in1, out):
        # INVAR: (in0 <op> in1) = out
        vars_ = [in0,in1,out]
        comment = (op.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)

        if out.symbol_type() == BOOL:
            bout = out
        else:
            bout = EqualsOrIff(out, BV(1, 1))
    
        invar = Iff(op(in0,in1), bout)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def LShl(in0,in1,out):
        return Modules.Bop(BVLShl,None,in0,in1,out)
    
    @staticmethod
    def LShr(in0,in1,out):
        return Modules.Bop(BVLShr,None,in0,in1,out)

    @staticmethod
    def AShr(in0,in1,out):
        return Modules.Bop(BVAShr,None,in0,in1,out)

    @staticmethod
    def Add(in0,in1,out):
        return Modules.Bop(BVAdd,None,in0,in1,out)

    @staticmethod
    def And(in0,in1,out):
        return Modules.Bop(BVAnd,And,in0,in1,out)

    @staticmethod
    def Xor(in0,in1,out):
        return Modules.Bop(BVXor,Xor,in0,in1,out)
    
    @staticmethod
    def Or(in0,in1,out):
        return Modules.Bop(BVOr,Or,in0,in1,out)
    
    @staticmethod
    def Sub(in0,in1,out):
        return Modules.Bop(BVSub,None,in0,in1,out)

    @staticmethod
    def Mul(in0,in1,out):
        return Modules.Bop(BVMul,None,in0,in1,out)

    @staticmethod
    def Ult(in0,in1,out):
        return Modules.BopBool(BVULT,in0,in1,out)
    
    @staticmethod
    def Ule(in0,in1,out):
        return Modules.Bop(BVUle,None,in0,in1,out)
    
    @staticmethod
    def Ugt(in0,in1,out):
        return Modules.BopBool(BVUGT,in0,in1,out)
    
    @staticmethod
    def Uge(in0,in1,out):
        return Modules.BopBool(BVUGE,in0,in1,out)
    
    @staticmethod
    def Slt(in0,in1,out):
        return Modules.Bop(BVSlt,None,in0,in1,out)
    
    @staticmethod
    def Sle(in0,in1,out):
        return Modules.Bop(BVSle,None,in0,in1,out)
    
    @staticmethod
    def Sgt(in0,in1,out):
        return Modules.Bop(BVSgt,None,in0,in1,out)
    
    @staticmethod
    def Sge(in0,in1,out):
        return Modules.Bop(BVSge,None,in0,in1,out)

    @staticmethod
    def Zext(in_,out):
        # INVAR: (<op> in) = out)
        vars_ = [in_,out]
        comment = ("ZExt (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)

        if (in_.symbol_type() == BOOL) and (out.symbol_type() == BOOL):
            invar = EqualsOrIff(in_, out)

        if (in_.symbol_type() != BOOL) and (out.symbol_type() == BOOL):
            invar = EqualsOrIff(BV2B(in_), out)

        if (in_.symbol_type() == BOOL) and (out.symbol_type() != BOOL):
            length = (out.symbol_type().width)-1
            if length == 0:
                invar = EqualsOrIff(in_, BV2B(out))
            else:
                invar = EqualsOrIff(BVZExt(B2BV(in_), length), out)

        if (in_.symbol_type() != BOOL) and (out.symbol_type() != BOOL):
            length = (out.symbol_type().width)-(in_.symbol_type().width)
            if length == 0:
                invar = EqualsOrIff(in_, out)
            else:
                invar = EqualsOrIff(BVZExt(in_, length), out)
                
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    @staticmethod
    def Const(out, value):
        invar = TRUE()
        if value is not None:
            if out.symbol_type() == BOOL:
                const = TRUE() if value == 1 else FALSE()
            else:
                const = BV(value, out.symbol_type().width)
            invar = EqualsOrIff(out, const)
            
        comment = "Const (out, val) = (" + out.symbol_name() + ", " + str(value) + ")"
        Logger.log(comment, 2)
        ts = TS(set([out]), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Clock(clk):
        # INIT: clk = 0
        # TRANS: clk' = !clk
        comment = "Clock (clk) = (" + clk.symbol_name() + ")"

        if clk.symbol_type() == BOOL:
            clk0 = Not(clk)
            clk1 = clk
        else:
            clk0 = EqualsOrIff(clk, BV(0, 1))
            clk1 = EqualsOrIff(clk, BV(1, 1))
        
        init = clk0

        invar = TRUE()
        
        if False:
            trans = EqualsOrIff(clk0, TS.to_next(clk1))
        else:
            # Implementation that leverages on the boolean propagation
            trans1 = Implies(clk0, TS.to_next(clk1))
            trans2 = Implies(clk1, TS.to_next(clk0))
            trans = And(trans1, trans2)

        if Modules.abstract_clock:
            invar = clk0
            init = TRUE()
            trans = TRUE()
            
        ts = TS(set([clk]), init, trans, invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Reg(in_, clk, clr, rst, out, initval):
        # INIT: out = initval
        # TRANS: ((!clk & clk') -> (((clr) -> (out' = 0)) & ((rst & !clr) -> (out' = initval)) & ((!rst & !clr) -> (out' = in)))) & 
        #        (!(!clk & clk') -> (out' = out)))
        # trans gives priority to clr signal over rst
        vars_ = [in_,clk,clr,rst,out]
        comment = "Reg (in, clk, clr, rst, out) = (%s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 2)

        init = TRUE()
        trans = TRUE()
        
        initvar = None
        initname = SEP.join(out.symbol_name().split(SEP)[:-1])+SEP+INIT
        
        if out.symbol_type() == BOOL:
            out0 = FALSE()
            initvar = Symbol(initname, BOOL)
        else:
            out0 = BV(0, out.symbol_type().width)
            initvar = Symbol(initname, _BVType(out.symbol_type().width))

        trans = And(trans, EqualsOrIff(initvar, TS.get_prime(initvar)))
        init = EqualsOrIff(out, initvar)
            
        if initval is not None:
            if out.symbol_type() == BOOL:
                binitval = FALSE() if initval == 0 else TRUE()
            else:
                binitval = BV(initval, out.symbol_type().width)

            init = And(init, EqualsOrIff(initvar, binitval))
        
        if clr is not None:
            if clr.symbol_type() == BOOL:
                clr0 = Not(clr)
                clr1 = clr
            else:
                clr0 = EqualsOrIff(clr, BV(0, 1))
                clr1 = EqualsOrIff(clr, BV(1, 1))
        else:
            clr0 = TRUE()
            clr1 = FALSE()

        if rst is not None:
            if rst.symbol_type() == BOOL:
                rst0 = Not(rst)
                rst1 = rst
            else:
                rst0 = EqualsOrIff(rst, BV(0, 1))
                rst1 = EqualsOrIff(rst, BV(1, 1))
        else:
            rst0 = TRUE()
            rst1 = FALSE()

        if clk.symbol_type() == BOOL:
            clk0 = Not(clk)
            clk1 = clk
        else:
            clk0 = EqualsOrIff(clk, BV(0, 1))
            clk1 = EqualsOrIff(clk, BV(1, 1))

        if Modules.abstract_clock:
            ri_clk = TRUE()
            do_clk = FALSE()
        else:
            ri_clk = And(clk0, TS.to_next(clk1))
            do_clk = And(clk1, TS.to_next(clk0))

        tr_clr = Implies(clr1, EqualsOrIff(TS.get_prime(out), out0))
        tr_rst_nclr = Implies(And(rst1, clr0), EqualsOrIff(TS.get_prime(out), initvar))
        tr_nrst_nclr = Implies(And(rst0, clr0), EqualsOrIff(TS.get_prime(out), in_))
        trans_ri = And(tr_clr, tr_rst_nclr, tr_nrst_nclr)
        trans_do = EqualsOrIff(out, TS.get_prime(out))
                
        trans = And(trans, Implies(ri_clk, trans_ri), Implies(do_clk, trans_do))
        trans = simplify(trans)
        ts = TS(set([initvar]+[v for v in vars_ if v is not None]), init, trans, TRUE())
        ts.state_vars = set([out])
        ts.comment = comment
        return ts

    @staticmethod
    def Mux(in0, in1, sel, out):
        # INVAR: ((sel = 0) -> (out = in0)) & ((sel = 1) -> (out = in1))
        vars_ = [in0,in1,sel,out]
        comment = "Mux (in0, in1, sel, out) = (%s, %s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
        
        if sel.symbol_type() == BOOL:
            sel0 = Not(sel)
            sel1 = sel
        else:            
            sel0 = EqualsOrIff(sel, BV(0, 1))
            sel1 = EqualsOrIff(sel, BV(1, 1))
            
        invar = And(Implies(sel0, EqualsOrIff(in0, out)), Implies(sel1, EqualsOrIff(in1, out)))
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Eq(in0, in1, out):
        # INVAR: (((in0 = in1) -> (out = #b1)) & ((in0 != in1) -> (out = #b0)))
        vars_ = [in0,in1,out]
        comment = "Eq (in0, in1, out) = (%s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
        eq = EqualsOrIff(in0, in1)

        if out.symbol_type() == BOOL:
            out0 = Not(out)
            out1 = out
        else:
            out0 = EqualsOrIff(out, BV(0, 1))
            out1 = EqualsOrIff(out, BV(1, 1))

        invar = And(Implies(eq, out1), Implies(Not(eq), out0))
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Neq(in0, in1, out):
        # INVAR: (((in0 != in1) -> (out = #b1)) & ((in0 == in1) -> (out = #b0)))
        vars_ = [in0,in1,out]
        comment = "Eq (in0, in1, out) = (%s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
        eq = EqualsOrIff(in0, in1)

        if out.symbol_type() == BOOL:
            out0 = Not(out)
            out1 = out
        else:
            out0 = EqualsOrIff(out, BV(0, 1))
            out1 = EqualsOrIff(out, BV(1, 1))

        invar = And(Implies(Not(eq), out1), Implies(eq, out0))
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Orr(in_, out):
        # INVAR: (in = 0) -> (out = 0) & (in != 0) -> (out = 1)
        vars_ = [in_, out]
        comment = "Orr (in, out) = (%s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)

        if (in_.symbol_type() == BOOL) and (out.symbol_type() == BOOL):
            invar = EqualsOrIff(in_, out)
        else:
            
            if out.symbol_type() == BOOL:
                out0 = Not(out)
                out1 = out
            else:
                out0 = EqualsOrIff(out, BV(0,1))
                out1 = EqualsOrIff(out, BV(1,1))
            
            true_res = Implies(EqualsOrIff(in_, BV(0,in_.symbol_type().width)), out0)
            false_res = Implies(Not(EqualsOrIff(in_, BV(0,in_.symbol_type().width))), out1)
            
            invar = And(true_res, false_res)
            
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Andr(in_, out):
        # INVAR: (in = 1) -> (out = 1) & (in != 1) -> (out = 0)
        vars_ = [in_, out]
        comment = "Andr (in, out) = (%s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
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
        comment = "Mux (in, out, low, high) = (%s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 2)
        invar = EqualsOrIff(BVExtract(in_, low, high), out)
        ts = TS(set([in_, out]), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    
class CoreIRParser(object):

    file = None
    context = None

    attrnames = None
    boolean = False
    
    def __init__(self, file, *libs):
        self.context = coreir.Context()
        for lib in libs:
            self.context.load_library(lib)

        self.file = file

        self.__init_attrnames()

        self.boolean = False

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



    def BVVar(self, name, width):
        if width <= 0 or not isinstance(width, int):
            raise UndefinedTypeException("Bit Vector undefined for width = {}".format(width))

        name = name.replace(CSEP, SEP)
        
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
        mod_map.append(("neq",   (Modules.Neq,   [self.IN0, self.IN1, self.OUT])))

        mod_map.append(("ult",  (Modules.Ult,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ule",  (Modules.Ule,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("ugt",  (Modules.Ugt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("uge",  (Modules.Uge,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("slt",  (Modules.Slt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sle",  (Modules.Sle,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sgt",  (Modules.Sgt,  [self.IN0, self.IN1, self.OUT])))
        mod_map.append(("sge",  (Modules.Sge,  [self.IN0, self.IN1, self.OUT])))
        
        mod_map.append(("const",  (Modules.Const, [self.OUT, self.VALUE])))
        mod_map.append(("reg",    (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.OUT, self.INIT])))
        mod_map.append(("regrst", (Modules.Reg, [self.IN, self.CLK, self.CLR, self.RST, self.OUT, self.INIT])))
        mod_map.append(("mux",    (Modules.Mux, [self.IN0, self.IN1, self.SEL, self.OUT])))
        mod_map.append(("slice",  (Modules.Slice, [self.IN, self.OUT, self.LOW, self.HIGH])))
        
        mod_map = dict(mod_map)

        ts = None
        
        if inst_type in mod_map:
            ts = mod_map[inst_type][0](*args(mod_map[inst_type][1]))

        return ts

    def parse_formula(self, strformula):
        formula = strformula.replace("\\","")
        for lit in re.findall("([a-zA-Z][a-zA-Z_$\.0-9]*)+", formula):
            if lit in KEYWORDS:
                continue
            formula = formula.replace(lit, "\'%s\'"%lit)

        return parse(formula)
    
    def parse(self, abstract_clock=False):
        Logger.msg("Reading CoreIR system... ", 1)
        top_module = self.context.load_from_file(self.file)

        Modules.abstract_clock = abstract_clock
        
        top_def = top_module.definition
        interface = list(top_module.type.items())
        modules = {}

        not_defined_mods = []

        hts = HTS(top_module.name)

        Logger.msg("Starting encoding... ", 1)

        totalinst = len(top_def.instances)
        count = 0
        
        for inst in top_def.instances:
            count += 1
            if count % 1000 == 0:
                Logger.msg("..converted %.2f%%"%(float(count*100)/float(totalinst)), 1)
            
            ts = None
            
            inst_name = inst.selectpath
            inst_type = inst.module.name
            inst_intr = dict(inst.module.type.items())
            modname = (SEP.join(inst_name))+SEP

            values_dic = {}

            for x in self.attrnames:
                if x in inst_intr:
                    values_dic[x] = self.BVVar(modname+x, inst_intr[x].size)
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
                if inst_type not in not_defined_mods:
                    intface = ", ".join(["%s"%(v) for v in values_dic if values_dic[v] is not None])
                    Logger.error("Module type \"%s\" with interface \"%s\" is not defined"%(inst_type, intface))
                    not_defined_mods.append(inst_type)
                
        for var in interface:
            varname = SELF+SEP+var[0]
            bvvar = self.BVVar(varname, var[1].size)
            hts.add_var(bvvar)
            if(var[1].is_input()):
                hts.inputs.add(bvvar)
            else:
                hts.outputs.add(bvvar)

            # Adding clock behavior
            if var[0].lower() == self.CLK:
                hts.add_ts(Modules.Clock(bvvar))

        varmap = dict([(s.symbol_name(), s) for s in hts.vars])

        def split_paths(path):
            ret = []
            for el in path:
                ret += el.split(CSEP)

            return ret

        def dict_select(dic, el):
            return dic[el] if el in dic else None
        
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

            first = dict_select(varmap, firstname)
            second = dict_select(varmap, secondname)
                
            if (first is None) and (second is not None):
                Logger.error("Symbol \"%s\" is not defined"%firstname)
                first = Symbol(firstname, second.symbol_type())
            else:
                if (is_number(first_selectpath[-1])) and (first.symbol_type() != BOOL):
                    sel = int(first_selectpath[-1])
                    first = BVExtract(first, sel, sel)


            if (first is not None) and (second is None):
                Logger.error("Symbol \"%s\" is not defined"%secondname)
                second = Symbol(secondname, first.symbol_type())
            else:
                if (is_number(second_selectpath[-1])) and (second.symbol_type() != BOOL):
                        sel = int(second_selectpath[-1])
                        second = BVExtract(second, sel, sel)

            assert((first is not None) and (second is not None))
                
            firstvar = first
            secondvar = second
                
            if (first.get_type() != BOOL) and (second.get_type() == BOOL):
                second = Ite(second, BV(1,1), BV(0,1))

            if (first.get_type() == BOOL) and (second.get_type() != BOOL):
                first = Ite(first, BV(1,1), BV(0,1))

                
            eq = EqualsOrIff(first, second)

            Logger.log(str(eq), 2)

            ts = TS(set([firstvar, secondvar]), TRUE(), TRUE(), eq)
            ts.comment = "Connection (%s, %s)"%(SEP.join(first_selectpath), SEP.join(second_selectpath))
            hts.add_ts(ts)

        return hts
