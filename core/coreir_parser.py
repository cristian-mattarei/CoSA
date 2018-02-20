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

from pysmt.shortcuts import get_env, Symbol, Iff, Not, BVAnd, EqualsOrIff, TRUE, FALSE, And, BV, Implies, BVExtract
from pysmt.typing import BOOL, _BVType
from pysmt.smtlib.printers import SmtPrinter

from core.transition_system import TS
from util.utils import is_number
from util.logger import Logger
from six.moves import cStringIO


SEP = "$"

ADD   = "add"
CONST = "const"
REG   = "reg"


def BVVar(name, width):
    if width <= 0 or not isinstance(width, int):
        raise UndefinedTypeException("Bit Vector undefined for width = {}".format(width))

    return Symbol(name, _BVType(width))

class SMTModules(object):

    @staticmethod
    def assert_op(expr):
        return "(assert "+ expr + ")"

    @staticmethod
    def binary_op_eqass(op, in1, in2, out):
        return SMTModules.assert_op("(= (" + op + " " + in1 + " " + in2 + ") " + out + ")")

    @staticmethod
    def SMTBop(op, in0, in1, out):
      # INIT: TRUE
      # TRANS: ((in0 <op> in1) = out) & ((in0' & in1') = out')
      comment = ";; " + op.__name__ + " (in0, in1, out) = (" + in0.symbol_name() + ", " + in1.symbol_name() + ", " + out.symbol_name() + ")"
      formula = EqualsOrIff(op(in0,in1), out)
      ts = TS(formula.get_free_variables(), TRUE(), TRUE(), formula)
      ts.comment = comment
      return ts

    @staticmethod
    def Add(in0,in1,out):
        return SMTModules.SMTBop(BVAnd,in0,in1,out)

    @staticmethod
    def Const(out, value):
        const = BV(value, out.symbol_type().width)
        formula = EqualsOrIff(out, const)
        comment = ";; Const (out, val) = (" + out.symbol_name() + ", " + str(const) + ")"
        ts = TS(formula.get_free_variables(), TRUE(), TRUE(), formula)
        ts.comment = comment
        return ts


    @staticmethod
    def Reg(in_, clk, clr, out):
      # INIT: out = 0
      # TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      comment = ";; Reg (in, clk, out) = (" + in_.symbol_name() + ", " + clk.symbol_name() + ", " + out.symbol_name() + ")"
      ival = BV(0, out.symbol_type().width)
      init = EqualsOrIff(out, ival)
      bclk = EqualsOrIff(clk, BV(1, 1))
      
      trans_1 = Implies(And(Not(bclk), TS.to_next(bclk)), EqualsOrIff(TS.get_prime(out), in_))
      trans_2 = Implies(Not(And(Not(bclk), TS.to_next(bclk))), EqualsOrIff(TS.get_prime(out), out))
      
      trans = And(trans_1, trans_2)
      ts = TS(trans.get_free_variables(), init, trans, TRUE())
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

        var_defs = []
        mod_defs = []

        top_module = self.context.load_from_file(self.file)
        top_def = top_module.definition
        interface = list(top_module.type.items())
        print(top_module.type, interface[0][1].kind)
        modules = {}
        quit(0)

        for inst in top_def.instances:
            inst_name = inst.selectpath
            inst_type = inst.module.name
            inst_args = inst.module.generator_args
            inst_intr = list(inst.module.type.items())
            modname = (SEP.join(inst_name))+SEP

            if inst_type == ADD:
                in0 = BVVar(modname+inst_intr[0][0], inst_intr[0][1].size)
                in1 = BVVar(modname+inst_intr[1][0], inst_intr[1][1].size)
                out = BVVar(modname+inst_intr[2][0], inst_intr[2][1].size)
                ts = SMTModules.Add(in0,in1,out)
                mod_defs.append(ts)
                var_defs += ts.vars
                continue

            if inst_type == CONST:
                value = inst.config["value"].value.val
                out = BVVar(modname+inst_intr[0][0], inst_intr[0][1].size)
                ts = SMTModules.Const(out,value)
                mod_defs.append(ts)
                var_defs += ts.vars
                continue

            if inst_type == REG:
                clk = BVVar(modname+inst_intr[0][0], inst_intr[0][1].size)
                clr = BVVar(modname+inst_intr[1][0], inst_intr[1][1].size)
                in_ = BVVar(modname+inst_intr[2][0], inst_intr[2][1].size)
                out = BVVar(modname+inst_intr[3][0], inst_intr[3][1].size)
                
                ts = SMTModules.Reg(in_, clk, clr, out)
                mod_defs.append(ts)
                var_defs += ts.vars
                continue
            
            Logger.log("*** MODULE TYPE \"%s\" IS NOT DEFINED!!"%(inst_type), 0)


        varmap = dict([(s.symbol_name(), s) for s in var_defs])
            
        for var_def in set(var_defs):
            print(str(var_def))
            print(str(TS.get_prime(var_def)))

        buf = cStringIO()
        printer = SmtPrinter(buf)
            
        for mod_def in mod_defs:
            mod_def.inline_invar()
            print(mod_def.comment)

            printer.printer(mod_def.init)
            print(SMTModules.assert_op(buf.getvalue()))
            buf.truncate(0)
            
            printer.printer(mod_def.trans)
            print(SMTModules.assert_op(buf.getvalue()))
            buf.truncate(0)

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
            
            printer.printer(eq)
            print(SMTModules.assert_op(buf.getvalue()))
            buf.truncate(0)

        return var_defs, mod_defs
