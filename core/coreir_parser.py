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

from pysmt.shortcuts import get_env, Symbol, Iff, Not, BVAnd, EqualsOrIff, TRUE, FALSE, And, BV, Implies, BVExtract, BVSub
from pysmt.typing import BOOL, _BVType
from pysmt.smtlib.printers import SmtPrinter

from core.transition_system import TS, HTS, SEP
from util.utils import is_number
from util.logger import Logger
from six.moves import cStringIO


ADD   = "add"
CONST = "const"
REG   = "reg"
MUX   = "mux"
SUB   = "sub"
EQ    = "eq"

def BVVar(name, width):
    if width <= 0 or not isinstance(width, int):
        raise UndefinedTypeException("Bit Vector undefined for width = {}".format(width))

    return Symbol(name, _BVType(width))

class Modules(object):

    @staticmethod
    def SMTBop(op, in0, in1, out):
      # INVAR: ((in0 <op> in1) = out) & ((in0' & in1') = out')
      vars_ = [in0,in1,out]
      comment = (";; " + op.__name__ + " (in0, in1, out) = (%s, %s, %s)")%(tuple([x.symbol_name() for x in vars_]))
      invar = EqualsOrIff(op(in0,in1), out)
      ts = TS(set(vars_), TRUE(), TRUE(), invar)
      ts.comment = comment
      return ts

    @staticmethod
    def Add(in0,in1,out):
        return Modules.SMTBop(BVAnd,in0,in1,out)

    @staticmethod
    def Sub(in0,in1,out):
        return Modules.SMTBop(BVSub,in0,in1,out)
    
    @staticmethod
    def Const(out, value):
        const = BV(value, out.symbol_type().width)
        formula = EqualsOrIff(out, const)
        comment = ";; Const (out, val) = (" + out.symbol_name() + ", " + str(const) + ")"
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
    def Reg(in_, clk, clr, out, initval):
      # INIT: out = initval
      # TRANS: (((!clk & clk') -> ((!clr -> (out' = in)) & (clr -> (out' = 0)))) & (!(!clk & clk') -> (out' = out)))
      vars_ = [in_,clk,clr,out]
      comment = ";; Reg (in, clk, clr, out) = (%s, %s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
      binitval = BV(initval, out.symbol_type().width)
      init = EqualsOrIff(out, binitval)
      bclk = EqualsOrIff(clk, BV(1, 1))
      bclr = EqualsOrIff(clr, BV(1, 1))
      zero = BV(0, out.symbol_type().width)

      trans_0 = And(Implies(Not(bclr), EqualsOrIff(TS.get_prime(out), in_)), Implies(bclr, EqualsOrIff(TS.get_prime(out), zero)))
      trans_1 = Implies(And(Not(bclk), TS.to_next(bclk)), trans_0)
      trans_2 = Implies(Not(And(Not(bclk), TS.to_next(bclk))), EqualsOrIff(TS.get_prime(out), out))
      
      trans = And(trans_1, trans_2)
      ts = TS(set(vars_), init, trans, TRUE())
      ts.comment = comment
      return ts

    @staticmethod
    def Mux(in0, in1, sel, out):
      # INVAR: ((sel = 0) -> (out = in0)) & ((sel = 1) -> (out = in1))
      vars_ = [in0,in1,sel,out]
      comment = ";; Mux (in0, in1, sel, out) = (%s, %s, %s, %s)"%(tuple([x.symbol_name() for x in vars_]))
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
      eq = EqualsOrIff(in0, in1)
      zero = EqualsOrIff(out, BV(0, 1))
      one = EqualsOrIff(out, BV(1, 1))
      invar = And(Implies(eq, one), Implies(Not(eq), zero))
      ts = TS(set(vars_), TRUE(), TRUE(), invar)
      ts.comment = comment
      return ts
  
    
class CoreIRParser(object):

    file = None
    context = None

    def __init__(self, file, *libs):
        self.context = coreir.Context()
        for lib in libs:
            self.context.load_library(lib)

        self.file = file

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
            #inst_args = inst.module.generator_args
            inst_intr = dict(inst.module.type.items())
            modname = (SEP.join(inst_name))+SEP

            keywords = "in"
            for x in ["in0", "in1", "out", "clk", "clr", "in", "out", "sel"]:
                if x in inst_intr:
                    setattr(self, x+("_" if x in keywords else ""), BVVar(modname+x, inst_intr[x].size))

            for x in ["init", "value"]:
                if x in inst.config:
                    xval = inst.config[x].value
                    if type(xval) == bool:
                        xval = 1 if xval else 0
                    else:
                        xval = xval.val
                    
                    setattr(self, x, xval)
                    
                    
            if inst_type == ADD:
                ts = Modules.Add(self.in0, self.in1, self.out)

            if inst_type == SUB:
                ts = Modules.Sub(self.in0, self.in1, self.out)

            if inst_type == EQ:
                ts = Modules.Eq(self.in0, self.in1, self.out)
                
            if inst_type == CONST:
                ts = Modules.Const(self.out, self.value)

            if inst_type == REG:
                ts = Modules.Reg(self.in_, self.clk, self.clr, self.out, self.init)

            if inst_type == MUX:
                ts = Modules.Mux(self.in0, self.in1, self.sel, self.out)
                
            if ts is not None:
                hts.add_ts(ts)
            else:                
                Logger.error("Module type \"%s\" is not defined"%(inst_type))
                
        for var in interface:
            varname = "self"+SEP+var[0]
            bvvar = BVVar(varname, var[1].size)
            hts.add_var(bvvar)

            # Adding clock behavior 
            if var[0] == "clk":
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

            hts.add_ts(TS(set([]), TRUE(), TRUE(), eq))

        return hts
