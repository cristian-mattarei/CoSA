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

from pysmt.shortcuts import get_env, Symbol, BV, simplify, \
    TRUE, FALSE, \
    And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, \
    BVExtract, BVSub, BVOr, BVAdd, BVXor, BVMul, BVNot, BVZExt, \
    BVLShr, BVLShl, BVAShr, BVULT, BVUGT, BVUGE, BVULE, BVConcat, \
    Array, Select, Store

from pysmt.typing import BOOL, _BVType, ArrayType
from pysmt.smtlib.printers import SmtPrinter

from cosa.core.transition_system import TS, HTS
from cosa.util.utils import is_number
from cosa.util.logger import Logger

SELF = "self"
INIT = "init"

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
        return Modules.BopBool(BVULE,in0,in1,out)
    
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
    def Concat(in0,in1,out):
        return Modules.Bop(BVConcat,None,in0,in1,out)

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
    def Reg(in_, clk, clr, rst, arst, out, initval, clk_posedge, arst_posedge):
        # INIT: out = initval
        
        # inr = Ite(clr, 0, Ite(rst, initval, in))
        # do_arst = Ite(arst_posedge, (!arst & arst'), (arst & !arst'))
        # do_clk = Ite(clk_posedge, (!clk & clk'), (clk & !clk'))
        # act_trans = (out' = inr)
        # pas_trans = (out' = out)
        
        # TRANS: (!do_arst -> ((do_clk -> act_trans) & (!do_clk -> pas_trans))) & (do_arst -> (out' = initval))
        # INVAR: True
        # trans gives priority to clr signal over rst

        vars_ = [in_,clk,clr,rst,arst,out]
        comment = "Reg (in, clk, clr, rst, arst, out) = (%s, %s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 2)

        init = TRUE()
        trans = TRUE()
        invar = TRUE()
            
        initvar = None
        basename = SEP.join(out.symbol_name().split(SEP)[:-1]) if SEP in out.symbol_name() else out.symbol_name()
        initname = basename+SEP+INIT

        if initval is not None:
            if out.symbol_type() == BOOL:
                binitval = FALSE() if initval == 0 else TRUE()
            else:
                binitval = BV(initval, out.symbol_type().width)

            initvar = binitval
        else:
            if out.symbol_type() == BOOL:
                initvar = Symbol(initname, BOOL)
            else:
                initvar = Symbol(initname, _BVType(out.symbol_type().width))

            trans = And(trans, EqualsOrIff(initvar, TS.get_prime(initvar)))
            vars_.append(initvar)

        init = And(init, EqualsOrIff(out, initvar))

        if arst_posedge is not None:
            arst_posedge0 = False if arst_posedge else True
            arst_posedge1 = True if arst_posedge else False
        else:
            arst_posedge0 = False
            arst_posedge1 = True

        if clk_posedge is not None:
            clk_posedge0 = False if clk_posedge else True
            clk_posedge1 = True if clk_posedge else False
        else:
            clk_posedge0 = False
            clk_posedge1 = True
            
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

        if arst is not None:
            if arst.symbol_type() == BOOL:
                arst0 = Not(arst)
                arst1 = arst
            else:
                arst0 = EqualsOrIff(arst, BV(0, 1))
                arst1 = EqualsOrIff(arst, BV(1, 1))
        else:
            arst0 = TRUE()
            arst1 = FALSE()

        if clk.symbol_type() == BOOL:
            clk0 = Not(clk)
            clk1 = clk
        else:
            clk0 = EqualsOrIff(clk, BV(0, 1))
            clk1 = EqualsOrIff(clk, BV(1, 1))

        if Modules.abstract_clock:
            do_clk = TRUE()
        else:
            do_clk = And(TS.to_next(clk1), clk0) if clk_posedge1 else And(TS.to_next(clk0), clk1)

        if out.symbol_type() == BOOL:
            out0 = FALSE()
        else:
            out0 = BV(0, out.symbol_type().width)

        inr = Ite(clr1, out0, Ite(rst1, initvar, in_))
        do_arst = And(TS.to_next(arst1), arst0) if arst_posedge1 else And(TS.to_next(arst0), arst1)
        ndo_arst = Not(do_arst)
        ndo_clk = Not(do_clk)
        act_trans = EqualsOrIff(inr, TS.get_prime(out))
        pas_trans = EqualsOrIff(out, TS.get_prime(out))
        
        trans = And(trans, And(Implies(ndo_arst, And(Implies(do_clk, act_trans), Implies(ndo_clk, pas_trans))), \
                    Implies(do_arst, EqualsOrIff(TS.get_prime(out), initvar))))
        
        trans = simplify(trans)
        ts = TS([v for v in vars_ if v is not None], init, trans, invar)
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
        # INVAR: (in = 2**width - 1) -> (out = 1) & (in != 2**width - 1) -> (out = 0)
        vars_ = [in_, out]
        comment = "Andr (in, out) = (%s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 2)
        width = in_.symbol_type().width
        eq_all_ones = EqualsOrIff(in_, BV(2**width - 1,width))
        true_res = Implies(eq_all_ones, EqualsOrIff(out, BV(1,1)))
        false_res = Implies(Not(eq_all_ones), EqualsOrIff(out, BV(0,1)))
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

    @staticmethod
    def Mem(clk, wdata, waddr, wen, rdata, raddr):
        # VAR: Array BV(waddr.width) BV(wdata.width)

        # INIT: True

        # do_clk = (!clk & clk')
        # act_read = (rdata' = Select(Array, raddr))
        # act_write = (Array' = Ite(wen, Store(array, waddr, wdata), Array))
        # act_trans = act_read & act_write
        # pas_trans = (rdata' = rdata) & (Array' = Array)

        # TRANS: (do_clk -> act_trans) & (!do_clk -> pas_trans)
        # INVAR: True
        # one cycle delay on read and write

        vars_ = [clk, wdata, waddr, wen, rdata, raddr]
        comment = "Mem (clk, wdata, waddr, wen, rdata, raddr) = (%s, %s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 2)

        init = TRUE()
        trans = TRUE()
        invar = TRUE()

        memname = SEP.join(rdata.symbol_name().split(SEP)[:-1]) if SEP in rdata.symbol_name() else rdata.symbol_name()

        arr = Symbol(memname + ".array", ArrayType(waddr.symbol_type(), wdata.symbol_type()))

        if clk.symbol_type() == BOOL:
            clk0 = Not(clk)
            clk1 = clk
        else:
            clk0 = EqualsOrIff(clk, BV(0, 1))
            clk1 = EqualsOrIff(clk, BV(1, 1))

        if wen.symbol_type() == BOOL:
            wen1 = wen
        else:
            wen1 = EqualsOrIff(wen, BV(1, 1))

        if Modules.abstract_clock:
            do_clk = TRUE()
        else:
            do_clk = And(TS.to_next(clk1), clk0)

        act_read = EqualsOrIff(TS.to_next(rdata), Select(arr, raddr))
        act_write = EqualsOrIff(TS.to_next(arr), Ite(wen1, Store(arr, waddr, wdata), arr))
        act_trans = And(act_read, act_write)
        pas_trans = And(EqualsOrIff(TS.to_next(rdata), rdata),
                        EqualsOrIff(TS.to_next(arr), arr))

        trans = And(Implies(do_clk, act_trans), Implies(Not(do_clk), pas_trans))
        trans = simplify(trans)
        ts = TS([v for v in vars_ if v is not None], init, trans, invar)
        ts.state_vars = set([arr])
        ts.comment = comment
        return ts


class CoreIRParser(object):

    file = None
    context = None

    attrnames = None
    boolean = False
    pack_connections = False
    anonimize_names = False
    map_an2or = None
    map_or2an = None
    idvars = 0
    
    def __init__(self, file, *libs):
        self.context = coreir.Context()
        for lib in libs:
            self.context.load_library(lib)

        self.file = file

        self.__init_attrnames()

        self.boolean = False
        self.pack_connections = True
        self.map_an2or = {}
        self.map_or2an = {}
        self.anonimize_names = False
        self.arrays = False
        
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
        
        mod_map = dict(mod_map)

        ts = None

        if inst_type in mod_map:
            ts = mod_map[inst_type][0](*args(mod_map[inst_type][1]))

        if ((args([self.CLK_POSEDGE])[0] == 0) or (args([self.ARST_POSEDGE])[0] == 0)) and Modules.abstract_clock:
            Logger.warning("Unsound clock abstraction: registers with negedge behavior")
            
        return ts
    
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
                        if type(xval) != int:
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
            if (self.CLK in var[0].lower()) and (var[1].is_input()):
                Logger.log("Adding clock behavior to \"%s\" input"%(varname), 1)
                hts.add_ts(Modules.Clock(bvvar))

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

            Logger.log(str(EqualsOrIff(first, second)), 2)

        ts = TS(eq_vars, TRUE(), TRUE(), eq_formula)
        ts.comment = "Connections" # (%s, %s)"%(SEP.join(first_selectpath), SEP.join(second_selectpath))
        hts.add_ts(ts)

        return hts


    def __pack_connections(self, connections):

        new_conns = []
        dict_conns = {}

        for conn in connections:
            (first, second) = (conn[0][0], conn[1][0])
            (sel1, sel2) = (conn[0][1], conn[1][1])

            if (first, second) not in dict_conns:
                dict_conns[(first, second)] = []
            
            dict_conns[(first, second)].append((sel1, sel2))


        for conn in dict_conns:
            (first,second) = conn
            conns = self.__analyze_connections(dict_conns[conn])

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
                return ((min_1, max_1), (min_2, max_2))

            d_min = (min_1 - min_2) if min_1 > min_2 else (min_2 - min_1)
            d_max = (max_1 - max_2) if max_1 > max_2 else (max_2 - max_1)

            # Transposed set e.g., [0,1,2,3] = [5,6,7,8]
            if (min_1 == inds_1[0]) and (min_2 == inds_2[0]) and (max_1 == inds_1[-1]) and (max_2 == inds_2[-1]) \
               and (d_min == d_max) and (len(inds_1) == len(inds_2)):
                return ((min_1, max_1), (min_2, max_2))
            
        return None
    

    
