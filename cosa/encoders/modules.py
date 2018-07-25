# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import get_env, Symbol, BV, simplify, \
    TRUE, FALSE, \
    And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, \
    BVExtract, BVSub, BVOr, BVAdd, BVXor, BVMul, BVNot, BVZExt, \
    BVLShr, BVLShl, BVAShr, BVULT, BVUGT, BVUGE, BVULE, BVConcat, \
    BVComp, Array, Select, Store
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.transition_systems import TS, HTS, L_BV, L_ABV
from cosa.utils.logger import Logger

SEP = "."
CSEP = "$"

SELF = "self"
INIT = "init"

def B2BV(var):
    return Ite(var, BV(1,1), BV(0,1))
    
def BV2B(var):
    return EqualsOrIff(var, BV(1,1))

class Modules(object):

    symbolic_init=False
    abstract_clock=False
    # control if encoding is functional
    functional = True
    # control whether encoding pushes ITE in array or bv theory
    array_ite = False
    
    @staticmethod
    def Uop(bvop, bop, in_, out):
        # INVAR: (<op> in) = out)
        vars_ = [in_,out]
        comment = (bvop.__name__ + " (in, out) = (%s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 3)

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
        Logger.log(comment, 3)
        invar = EqualsOrIff(in_, out)
        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts
    
    @staticmethod
    def Bop(bvop, bop, in0, in1, out):
        # INVAR: (in0 <op> in1) = out
        vars_ = [in0,in1,out]
        comment = (bvop.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 3)

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
        Logger.log(comment, 3)

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
        Logger.log(comment, 3)

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
        Logger.log(comment, 3)
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
        ts.state_vars = set([clk])
        ts.comment = comment
        return ts

    @staticmethod
    def Reg(in_, clk, clr, rst, arst, out, initval, clk_posedge, arst_posedge):
        # INIT: out = initval

        # do_arst = Ite(arst_posedge, (!arst & arst'), (arst & !arst'))
        # do_clk = Ite(clk_posedge, (!clk & clk'), (clk & !clk'))
        # inr = Ite(clr, 0, Ite(rst, initval, in))

        # if Modules.functional
        # TRANS: out' = Ite(do_clk, Ite(clr, 0, Ite(rst, initval, in)), Ite(rst, initval, in))
        # INVAR: True
        # trans gives priority to clr signal over rst

        # else
        # act_trans = (out' = inr)
        # pas_trans = (out' = out)
        # TRANS: (!do_arst -> ((do_clk -> act_trans) & (!do_clk -> pas_trans))) & (do_arst -> (out' = initval))
        # INVAR: True
        # trans gives priority to clr signal over rst

        vars_ = [in_,clk,clr,rst,arst,out]
        comment = "Reg (in, clk, clr, rst, arst, out) = (%s, %s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 3)

        init = TRUE()
        trans = TRUE()
        invar = TRUE()

        initvar = None
        basename = SEP.join(out.symbol_name().split(SEP)[:-1]) if SEP in out.symbol_name() else out.symbol_name()
        initname = basename+SEP+INIT

        if initval is not None and not Modules.symbolic_init:
            if out.symbol_type() == BOOL:
                binitval = FALSE() if initval == 0 else TRUE()
            else:
                binitval = BV(initval, out.symbol_type().width)

            initvar = binitval
        else:
            if out.symbol_type() == BOOL:
                initvar = Symbol(initname, BOOL)
            else:
                initvar = Symbol(initname, BVType(out.symbol_type().width))

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

        if Modules.functional:
            f_outr = Ite(rst1, initvar, out)
            f_inr = Ite(rst1, initvar, in_)
            f_clr_rst = Ite(clr1, out0, f_inr)
            trans = And(trans, EqualsOrIff(TS.get_prime(out), Ite(do_clk, f_clr_rst, f_outr)))
        else:
            trans = And(trans, And(Implies(ndo_arst, And(Implies(do_clk, act_trans), Implies(ndo_clk, pas_trans))), \
                                   Implies(do_arst, EqualsOrIff(TS.get_prime(out), initvar))))
        
        trans = simplify(trans)
        ts = TS([v for v in vars_ if v is not None], init, trans, invar)
        ts.state_vars = set([out])
        ts.comment = comment
        return ts

    @staticmethod
    def Mux(in0, in1, sel, out):
        # if Modules.functional
        # INVAR: out' = Ite(sel = 0, in0, in1)
        # else
        # INVAR: ((sel = 0) -> (out = in0)) & ((sel = 1) -> (out = in1))
        vars_ = [in0,in1,sel,out]
        comment = "Mux (in0, in1, sel, out) = (%s, %s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 3)
        
        if sel.symbol_type() == BOOL:
            sel0 = Not(sel)
            sel1 = sel
        else:            
            sel0 = EqualsOrIff(sel, BV(0, 1))
            sel1 = EqualsOrIff(sel, BV(1, 1))

        if Modules.functional:
            invar = And(EqualsOrIff(out, Ite(sel0, in0, in1)))
        else:
            invar = And(Implies(sel0, EqualsOrIff(in0, out)), Implies(sel1, EqualsOrIff(in1, out)))

        ts = TS(set(vars_), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Eq(in0, in1, out):
        # INVAR: (((in0 = in1) -> (out = #b1)) & ((in0 != in1) -> (out = #b0)))
        vars_ = [in0,in1,out]
        comment = "Eq (in0, in1, out) = (%s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
        Logger.log(comment, 3)

        if Modules.functional:
            if out.symbol_type() == BOOL:
                invar = EqualsOrIff(out, EqualsOrIff(in0, in1))
            else:
                invar = EqualsOrIff(out, BVComp(in0, in1))
        else:
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
        Logger.log(comment, 3)

        # TODO: Create functional encoding
        if Modules.functional:
            if out.symbol_type() == BOOL:
                invar = EqualsOrIff(out, Not(EqualsOrIff(in0, in1)))
            else:
                invar = EqualsOrIff(out, BVNot(BVComp(in0, in1)))
        else:
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
        Logger.log(comment, 3)

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
        Logger.log(comment, 3)
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
        Logger.log(comment, 3)
        invar = EqualsOrIff(BVExtract(in_, low, high), out)
        ts = TS(set([in_, out]), TRUE(), TRUE(), invar)
        ts.comment = comment
        return ts

    @staticmethod
    def Mem(clk, wdata, waddr, wen, rdata, raddr):
        # VAR: Array BV(waddr.width) BV(wdata.width)

        # INIT: True (doesn't handle initial value yet)
        # INVAR: (rdata = Select(Array, raddr))

        # do_clk = (!clk & clk')

        # if Modules.functional
        # TRANS: Array' = Ite(do_clk, Ite(wen, Store(Array, waddr, wdata), Array), Array)

        # else
        # act_trans = (Array' = Ite(wen, Store(Array, waddr, wdata), Array))
        # pas_trans = (Array' = Array)

        # TRANS: (do_clk -> act_trans) & (!do_clk -> pas_trans)
        # one cycle delay on write

        vars_ = [clk, wdata, waddr, wen, rdata, raddr]
        comment = "Mem (clk, wdata, waddr, wen, rdata, raddr) = (%s, %s, %s, %s, %s, %s)"%(tuple([str(x) for x in vars_]))
        Logger.log(comment, 3)

        init = TRUE()
        trans = TRUE()
        invar = TRUE()

        memname = SEP.join(rdata.symbol_name().split(SEP)[:-1]) if SEP in rdata.symbol_name() else rdata.symbol_name()

        arr = Symbol(memname + ".array", ArrayType(waddr.symbol_type(), wdata.symbol_type()))
        vars_.append(arr)

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

        invar = EqualsOrIff(rdata, Select(arr, raddr))

        if Modules.array_ite:
            next_arr = Ite(wen1, Store(arr, waddr, wdata), arr)
        else:
            next_arr = Store(arr, waddr, Ite(wen1, wdata, Select(arr, waddr)))

        if Modules.functional:
            trans = EqualsOrIff(TS.to_next(arr), Ite(do_clk, next_arr, arr))
        else:
            act_trans = EqualsOrIff(TS.to_next(arr), next_arr)
            pas_trans = EqualsOrIff(TS.to_next(arr), arr)
            trans = And(Implies(do_clk, act_trans), Implies(Not(do_clk), pas_trans))

        trans = simplify(trans)
        ts = TS([v for v in vars_ if v is not None], init, trans, invar)
        ts.state_vars = set([arr])
        ts.comment = comment
        ts.logic = L_ABV
        return ts

    def Term(_in):
        '''
        Term is a no-op. Just terminates a coreir wireable
        '''
        vars_ = [_in]
        init = TRUE()
        trans = TRUE()
        invar = TRUE()
        ts = TS(vars_, init, trans, invar)
        ts.state_vars = set()
        ts.comment = "Terminate wire"
        return ts

class ModuleSymbols(object):

    @staticmethod
    def Const(out, value):
        if value is None:
            return None
        if out.symbol_type() == BOOL:
            const = TRUE() if value == 1 else FALSE()
        else:
            const = BV(value, out.symbol_type().width)

        return (out, const)
