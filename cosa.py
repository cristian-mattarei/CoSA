import sys
import coreir
from six.moves import cStringIO

from pysmt.shortcuts import get_env, Symbol, Iff, Not, BVAnd, EqualsOrIff, TRUE, FALSE, And, BV
from pysmt.typing import BOOL, BV1, BV8, BV16, BV32, BV64, BV128
from pysmt.smtlib.printers import SmtPrinter

ADD   = "add"
CONST = "const"
REG   = "reg"

CURR_PF = "__CURR__"
NEXT = "_N"
NL = "\n"
SEP = "$"


class UndefinedTypeException(Exception):
    pass

def BVVar(name, width):
    if width == 1:
        return Symbol(name, BV1)
    elif width == 8:
        return Symbol(name, BV8)
    elif width == 16:
        return Symbol(name, BV16)
    elif width == 32:
        return Symbol(name, BV32)
    elif width == 64:
        return Symbol(name, BV64)
    elif width == 128:
        return Symbol(name, BV128)
    else:
        raise UndefinedTypeException

class TS(object):

    vars = None
    init = None
    trans = None
    invar = None
    
    comment = None
    
    def __init__(self, vars, init, trans, invar):
        self.vars = vars
        self.init = init
        self.trans = trans
        self.invar = invar

        self.comment = None

    def inline_invar(self):
        if self.invar is not None:
            self.trans = And([self.trans, self.invar, TS.to_next(self.invar)])

        self.invar = None

    @staticmethod
    def get_prime(v):
        return Symbol(("%s"+NEXT) % v.symbol_name(), v.symbol_type())

    @staticmethod
    def to_next(formula):
        varmap = dict([(v,TS.get_prime(v)) for v in formula.get_free_variables()])
        return formula.substitute(varmap)
    
    
class SmtBVVar(object):
    name = None
    size = None
    
    def __init__(self, name, size):
        self.name = name
        self.size = size

    def __repr__(self):
        return "%s (%s)"%(self.name, self.size)

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
    
def load_core(file, *libs):
    context = coreir.Context()
    for lib in libs:
        context.load_library(lib)


    var_defs = []
    mod_defs = []
        
    top_module = context.load_from_file(file)
    top_def = top_module.definition
    modules = {} 

    
    for inst in top_def.instances:
        inst_name = inst.selectpath
        inst_type = inst.module.name
        inst_args = inst.module.generator_args
        inst_intr = list(inst.module.type.items())
        modname = (SEP.join(inst_name))+SEP
        
#        print(inst_name, inst_type, "\n") #, list(inst_intr))  #list(inst.module.type.items())[0][1].size

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
        

        print("*** MODULE TYPE \"%s\" IS NOT DEFINED!!"%(inst_type))


    for var_def in set(var_defs):
        print(str(var_def))
        print(str(TS.get_prime(var_def)))

    for mod_def in mod_defs:
        buf = cStringIO()
        printer = SmtPrinter(buf)
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
        
        print(conn.first.selectpath, conn.second.selectpath)

        
    
    return var_defs, mod_defs


if __name__ == "__main__":
    
    load_core(sys.argv[1])
