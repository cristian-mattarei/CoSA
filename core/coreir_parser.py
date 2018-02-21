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
      init = EqualsOrIff(out, initval)
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

            if inst_type == ADD:
                in0 = BVVar(modname+"in0", inst_intr["in0"].size)
                in1 = BVVar(modname+"in1", inst_intr["in1"].size)
                out = BVVar(modname+"out", inst_intr["out"].size)
                ts = Modules.Add(in0,in1,out)

            if inst_type == SUB:
                in0 = BVVar(modname+"in0", inst_intr["in0"].size)
                in1 = BVVar(modname+"in1", inst_intr["in1"].size)
                out = BVVar(modname+"out", inst_intr["out"].size)
                ts = Modules.Sub(in0,in1,out)

            if inst_type == EQ:
                in0 = BVVar(modname+"in0", inst_intr["in0"].size)
                in1 = BVVar(modname+"in1", inst_intr["in1"].size)
                out = BVVar(modname+"out", inst_intr["out"].size)
                ts = Modules.Eq(in0,in1,out)
                
            if inst_type == CONST:
                value = inst.config["value"].value

                if type(value) == bool:
                    value = 1 if value else 0
                else:
                    value = value.val
                
                out = BVVar(modname+"out", inst_intr["out"].size)
                ts = Modules.Const(out,value)

            if inst_type == REG:
                clk = BVVar(modname+"clk", inst_intr["clk"].size)
                clr = BVVar(modname+"clr", inst_intr["clr"].size)
                in_ = BVVar(modname+"in", inst_intr["in"].size)
                out = BVVar(modname+"out", inst_intr["out"].size)
                ival = BV(inst.config["init"].value.val, out.symbol_type().width)
                ts = Modules.Reg(in_, clk, clr, out, ival)

            if inst_type == MUX:
                in0 = BVVar(modname+"in0", inst_intr["in0"].size)
                in1 = BVVar(modname+"in1", inst_intr["in1"].size)
                sel = BVVar(modname+"sel", inst_intr["sel"].size)
                out = BVVar(modname+"out", inst_intr["out"].size)
                ts = Modules.Mux(in0, in1, sel, out)
                
            if ts is not None:
                hts.add_ts(ts)
            else:                
                Logger.error("*** MODULE TYPE \"%s\" IS NOT DEFINED!!"%(inst_type))
                
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
