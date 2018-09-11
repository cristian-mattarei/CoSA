# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import re
import os
import math

VPARSER = True

try:
    from pyverilog.vparser.parser import VerilogParser, VerilogPreprocessor
    from pyverilog.vparser.plyparser import ParseError
    from pyverilog.vparser.ast import *
except:
    VPARSER = False

from pysmt.shortcuts import Symbol, BV, simplify, TRUE, FALSE, get_type, get_model, is_sat
from pysmt.shortcuts import And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, \
    BVExtract, BVAdd, BVConcat, BVULT, BVULE, BVUGT, BVUGE, BVXor, BVOr, BVLShl
from pysmt.fnode import FNode
from pysmt.typing import BOOL, BVType, ArrayType, INT
from pysmt.rewritings import conjunctive_partition

from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser
from cosa.walkers.verilog_walker import VerilogWalker
from cosa.representation import HTS, TS
from cosa.utils.generic import bin_to_dec, dec_to_bin
from cosa.utils.formula_mngm import B2BV, BV2B, get_free_variables, substitute, mem_access

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

MAXINT = 64

POSEDGE = "posedge"
NEGEDGE = "negedge"
LEVEL = "level"

INPUT = "input"
OUTPUT = "output"

class VerilogHTSParser(ModelParser):
    parser = None
    extensions = ["v"]
    name = "Verilog"

    files_from_dir = False
    
    def __init__(self):
        self.walker = VerilogSTSWalker()

    def is_available(self):
        return VPARSER

    def parse_file(self, strfile, config, flags=None):
        invar_props = []
        ltl_props = []

        if flags is None:
            Logger.error("Module name not provided")
        
        absstrfile = os.path.abspath(strfile)
        ast = self.parse([absstrfile])
        self.walker.config = config
        hts = self.walker.walk(ast, flags[0])
        hts.flatten()
        return (hts, invar_props, ltl_props)

    def get_extensions(self):
        return self.extensions

    def parse(self, filelist, preprocess_include=None, preprocess_define=None):
        codeparser = VerilogCodeParser(filelist,
                                       preprocess_include=preprocess_include,
                                       preprocess_define=preprocess_define)
        ast = codeparser.parse()
        return ast
    
    @staticmethod        
    def get_extensions():
        return VerilogHTSParser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

class VerilogCodeParser(object):

    def __init__(self, filelist, preprocess_output='preprocess.output',
                 preprocess_include=None,
                 preprocess_define=None):
        self.preprocess_output = preprocess_output
        self.directives = ()
        self.preprocessor = VerilogPreprocessor(filelist, preprocess_output,
                                                preprocess_include,
                                                preprocess_define)
        self.parser = VerilogParser()

    def preprocess(self):
        self.preprocessor.preprocess()
        with open(self.preprocess_output) as f:
            text = f.read()
        os.remove(self.preprocess_output)
        return text

    def parse(self, preprocess_output='preprocess.output', debug=0):
        text = self.preprocess()
        try:
            ast = self.parser.parse(text, debug=debug)
        except ParseError as e:
            Logger.error("Parsing at line %s"%(e))
        self.directives = self.parser.get_directives()
        return ast

    def get_directives(self):
        return self.directives
    
class VerilogSTSWalker(VerilogWalker):
    varmap = None
    paramdic = None
    subhtsdic = None
    modulesdic = None
    hts = None
    ts = None
    config = None
    
    id_vars = 0

    def __init__(self):
        self.reset_structures()

    def reset_structures(self, modulename=""):
        self.hts = HTS(modulename)
        self.ts = TS()
        self.portslist = None
        if self.varmap is None: self.varmap = {}
        if self.paramdic is None: self.paramdic = {}
        if self.modulesdic is None: self.modulesdic = {} 
        
    def _fresh_symbol(self, name):
        VerilogSTSWalker.id_vars += 1
        return "%s__%d"%(name, VerilogSTSWalker.id_vars)

    def add_constraint(self, constraint):
        if TS.has_next(constraint):
            self.ts.trans = And(self.ts.trans, constraint)
        else:
            self.ts.invar = And(self.ts.invar, constraint)
            
    def varname(self, modulename, varname):
        if modulename == "":
            return varname
        return "%s.%s"%(modulename, varname)
    
    def Paramlist(self, modulename, el, args):
        return el

    def Wire(self, modulename, el, args):
        width = args[0] if args is not None else 1
        self.add_var(modulename, el.name, Symbol(self.varname(modulename, el.name), BVType(width)))
        return (el.name, args)

    def Reg(self, modulename, el, args):
        width = args[0] if args is not None else 1
        self.add_var(modulename, el.name, Symbol(self.varname(modulename, el.name), BVType(width)))
        return (el.name, args)
    
    def Ioport(self, modulename, el, args):
        return (el.first, args)

    def Input(self, modulename, el, args):
        return (el.name, args)

    def Inout(self, modulename, el, args):
        return (el.name, args)
    
    def Output(self, modulename, el, args):
        return (el.name, args)

    def Port(self, modulename, el, args):
        return (None, [(el.name, None)])

    def Portlist(self, modulename, el, args):
        for port in args:
            porttype = port[0]
            portname = port[1][0][0]
            portsize = port[1][0][1]

            if porttype == None:
                if portsize is None:
                    self.add_var(modulename, portname, (None, INPUT))
                else:
                    width = portsize[0]
                    var = Symbol(self.varname(modulename, portname), BVType(width))
                    self.add_var(modulename, portname, var)
                    self.ts.add_input_var(var)
                continue
            
            if type(porttype) == Output:
                if portsize is None:
                    self.add_var(modulename, portname, (None, OUTPUT))
                else:
                    width = portsize[0]
                    var = Symbol(self.varname(modulename, portname), BVType(width))
                    self.add_var(modulename, portname, var)
                    self.ts.add_output_var(var)
                continue

            if type(porttype) == Input:
                if portsize is None:
                    self.add_var(modulename, portname, (None, INPUT))
                else:
                    width = portsize[0]
                    var = Symbol(self.varname(modulename, portname), BVType(width))
                    self.add_var(modulename, portname, var)
                    self.ts.add_input_var(var)
                continue
                    
            assert False

        self.portslist = [p[1][0][0] for p in args]

        return args

    def add_var(self, modulename, varname, value):
        self.varmap[varname] = value

    def get_var(self, modulename, varname, size=1):
        if type(self.varmap[varname]) == tuple:
            var = Symbol(self.varname(modulename,varname), BVType(size))
            if self.varmap[varname][1] == INPUT:
                self.ts.add_input_var(var)
            if self.varmap[varname][1] == OUTPUT:
                self.ts.add_output_var(var)
            self.varmap[varname] = var
            return var
        else:
            return self.varmap[varname]
        
    def Decl(self, modulename, el, args):
        if args[0] == None:
            return args

        direction = el.children()[0]

        if type(direction) in [Input, Output, Inout, Reg, Wire]:
            width = args[0][1]
            typ = el.children()[0]

            if width is None:
                if typ.name not in self.varmap:
                    Logger.error("Variable \"%s\" not defined, line %d"%(typ.name, el.lineno))
                var_inmap = self.varmap[typ.name]
                if type(var_inmap) == tuple:
                    width = 1 if var_inmap[0] is None else var_inmap[0]
                else:
                    width = var_inmap.symbol_type().width
            else:
                width = width[0]
            
            if typ.name in self.varmap:
                prev_width = self.varmap[typ.name][0] if type(self.varmap[typ.name]) is not FNode else self.varmap[typ.name].symbol_type().width
                if (prev_width is not None) and (prev_width != width):
                    Logger.error("Unmatched variable size at line %d"%el.lineno)

            var = Symbol(self.varname(modulename, typ.name), BVType(width))

            if type(direction) == Input:
                self.ts.add_input_var(var)
            elif type(direction) == Output:
                self.ts.add_output_var(var)
            else:
                self.ts.add_state_var(var)

            self.add_var(modulename, typ.name, var)

            return var

        if type(direction) == RegArray:
            low, high = args[0][1][1], args[0][1][0]
            low, high = min(low, high), max(low, high)
            width = args[0][0]
            vname = el.children()[0].name
            var_idxs = []
            just = len(str(high))
            for i in range(low, high+1, 1):
                vname_idx = "%s_%s"%(vname, str(i).rjust(just,"0"))
                var_idx = Symbol(self.varname(modulename, vname_idx), BVType(width))
                var_idxs.append(var_idx)
                self.add_var(modulename, vname_idx, var_idx)
                self.ts.add_state_var(var_idx)

            self.add_var(modulename, vname, var_idxs)
            self.ts.add_var(Symbol(self.varname(modulename, vname), BVType(width)))
                
            return var_idxs
        
        Logger.error("Unmanaged type %s, line %d"%(type(direction), el.lineno))
        
    def Sens(self, modulename, el, args):
        if el.sig is None:
            return TRUE()
            
        var = self.get_var(modulename, el.sig.name)

        zero = BV(0, var.symbol_type().width)
        one = BV(1, var.symbol_type().width)
        
        if el.type == POSEDGE:
            if self.config.abstract_clock:
                return TRUE()
            return And(EqualsOrIff(var, zero), EqualsOrIff(TS.get_prime(var), one))

        if el.type == NEGEDGE:
            if self.config.abstract_clock:
                Logger.warning("Unsound clock abstraction: registers with negedge behavior")

            return And(EqualsOrIff(var, one), EqualsOrIff(TS.get_prime(var), zero))

        if el.type == LEVEL:
            return EqualsOrIff(var, one)
        
        Logger.error("Unknown driver type \"%s\" at line %d"%(el.type, el.lineno))

    def Lvalue(self, modulename, el, args):
        return args[0]

    def Rvalue(self, modulename, el, args):
        return args[0]

    def NonblockingSubstitution(self, modulename, el, args):
        left, right = args[0], args[1]

        if type(right) == int:
            right = BV(right, get_type(left).width)

        if left.is_symbol():
            left = TS.to_next(left)
        else:
            primedic = dict([(v.symbol_name(), TS.get_prime(v).symbol_name()) for v in get_free_variables(left) \
                             if v not in self.ts.input_vars])
            left = substitute(left, primedic)
        
        return EqualsOrIff(left, right)

    def BlockingSubstitution(self, modulename, el, args):
        left, right = args[0], args[1]
        delay = 0
        
        if len(args) > 2:
            delay = args[2]
            
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)

        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        if type(left) == int:
            left = BV(left, MAXINT)
        if type(right) == int:
            right = BV(right, MAXINT)
            
        fv_left = get_free_variables(left)
        fv_right = get_free_variables(right)

        if delay == 1:
            left = TS.to_next(left)
        
        return EqualsOrIff(left, B2BV(right))

    def SensList(self, modulename, el, args):
        return Or(args)

    def Integer(self, modulename, el, args):
        intvar = Symbol(self.varname(modulename, el.name), BVType(MAXINT))
        self.add_var(modulename, el.name, intvar)
        return None
    
    def IntConst(self, modulename, el, args):
        if "'d" in el.value:
            width, value = el.value.split("'d")
            if width == "":
                return int(value)
            return BV(int(value), int(width))

        if "'b" in el.value:
            width, value = el.value.split("'b")
            if value == "z":
                if width == "":
                    Logger.error("High Bit value definition requires size, line %d"%el.lineno)
                value = dec_to_bin(int((2**int(width))-1), int(width))
            if width == "":
                return int(bin_to_dec(value))

            return BV(int(bin_to_dec(value)), int(width))
        
        return int(el.value)

    def Identifier(self, modulename, el, args):
        if el.name in self.paramdic:
            return self.paramdic[el.name]

        if el.name in self.varmap:
            return self.get_var(modulename, el.name)

        Logger.error("Symbol \"%s\" is not defined, line %d"%(el.name, el.lineno))
        return el.name
    
    def Width(self, modulename, el, args):
        return (args[0] - args[1])+1
    
    def Block(self, modulename, el, args):
        return And(args)

    def Cond(self, modulename, el, args):
        return Ite(args[0], args[1], args[2])
    
    def IfStatement(self, modulename, el, args):
        statement, then_b, else_b = args[0], args[1], args[2]

        if type(then_b) == list:
            Logger.error("Not Implemented")
        else:
            if type(statement) == int:
                condition = self.to_bool(statement)
            elif get_type(statement) == BOOL:
                condition = statement
            else:
                one = BV(1, get_type(statement).width)
                condition = EqualsOrIff(statement, one)

            if len(args) == 2:
                return Implies(condition, then_b)
            else:
                return Ite(condition, then_b, else_b)

    def Initial(self, modulename, el, args):
        self.ts.init = And(self.ts.init, And([And(a) for a in args]))
        return And(args)
            
    def Always(self, modulename, el, args):
        condition, statements = args[0], args[1]

        if type(statements) == FNode:
            statements = [statements]

        # All variables in the senselist are accessed at the primed time
        sensedict = dict([(v.symbol_name(), TS.get_prime(v).symbol_name()) \
                          for v in get_free_variables(condition) if not TS.is_prime(v)])
        for i in range(len(statements)):
            statements[i] = substitute(statements[i], sensedict)
        
        nonblocking = And([s for s in statements if TS.has_next(s)])
        blocking = And([s for s in statements if not TS.has_next(s)])

        def gen_formula(statement):
            if statement == TRUE():
                return TRUE()
            fv = [TS.get_ref_var(v) for v in get_free_variables(statement) if TS.is_prime(v)]
            frame_cond = And([EqualsOrIff(v, TS.get_prime(v)) for v in fv])
            active = statement if condition == TRUE() else Implies(condition, statement)
            passive = TRUE() if condition == TRUE() else Implies(Not(condition), frame_cond)
            return And(active, passive)

        self.ts.invar = And(self.ts.invar, gen_formula(blocking))
        self.ts.trans = And(self.ts.trans, gen_formula(nonblocking))
        
        return gen_formula(And(blocking, nonblocking)) #(condition, blocking, nonblocking)
    
    def ForStatement(self, modulename, el, args):

        # Refining definition in primed format e.g., for(i=0;i<10;i=i+1) into for(i'=0;i<10;i'=i+1)
        args[0] = args[0].substitute(dict([(v, TS.get_prime(v)) for v in get_free_variables(args[0])]))
        cp = list(conjunctive_partition(args[2]))
        newcp = []
        for ass in cp:
            left, right = ass.args()[0], ass.args()[1]
            assert (ass.is_equals() or ass.is_iff()) and (left.is_symbol() or right.is_symbol())
            if left.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(left), right))
            if right.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(right), left))

        args[2] = And(newcp)

        # Performining the For-loop unrolling
        fv = get_free_variables(args[0])
        model = get_model(args[0])
        state_n = [(v, model[v]) for v in fv]
        state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
        state = dict(state_c + state_n)
        formulae = []
        while True:
            # Evaluate new instance
            formula = simplify(And(args[3]).substitute(state))
            formulae.append(formula)

            # Compute next step
            model = get_model(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args[2]))
            state_n = [(v, model[v]) for v in fv]
            state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
            state = dict(state_c + state_n)

            # Exit condition
            if not is_sat(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args[1])):
                break

        return And(formulae)
    
    def ModuleDef(self, modulename, el, args):
        self.hts.add_ts(self.ts)

        self.portslist.sort()
        for param in self.portslist:
            self.hts.add_param(self.get_var(modulename, param))

        Logger.log("Ports module \"%s\": %s"%(el.name, ", ".join(["%s:%s"%(p, get_type(self.get_var(modulename, p))) for p in self.portslist])), 2)
        Logger.log("Parameters module \"%s\": %s"%(el.name, ", ".join(["%s=%s"%(p, self.paramdic[p]) for p in self.paramdic])), 2)
        return self.hts

    def Description(self, modulename, el, args):
        return args[0]

    def Source(self, modulename, el, args):
        return args[0]

    # TODO: Fix operations to manage both ints and BV
    def Divide(self, modulename, el, args):
        return int(int(args[0])/int(args[1]))

    def Minus(self, modulename, el, args):
        return int(args[0])-int(args[1])

    def Plus(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return left+right
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(right) == int):
            right = BV(right, MAXINT)
                    
        return BVAdd(left, right)
    
    def Eq(self, modulename, el, args):
        return EqualsOrIff(args[0], args[1])

    def NotEq(self, modulename, el, args):
        return Not(self.Eq(modulename, el, args))

    def to_bool(self, el):
        if type(el) == int:
            return FALSE() if el == 0 else TRUE()
        return BV2B(el)

    def to_bv(self, el):
        if type(el) == int:
            return BV(el, 1)
        return B2BV(el)
    
    def And(self, modulename, el, args):
        return BVAnd(self.to_bv(args[0]), self.to_bv(args[1]))

    def Land(self, modulename, el, args):
        return And([self.to_bool(x) for x in args])
    
    def Xor(self, modulename, el, args):
        return BVXor(self.to_bv(args[0]), self.to_bv(args[1]))

    def Or(self, modulename, el, args):
        return BVOr(self.to_bv(args[0]), self.to_bv(args[1]))

    def Lor(self, modulename, el, args):
        return Or([self.to_bool(x) for x in args])
    
    def Sll(self, modulename, el, args):
        left, right = args[0], args[1]
        if (type(left) == int) and (type(right) == int):
            return left << right
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
        
        return BVLShl(left, right)
        
    def LessThan(self, modulename, el, args):
        left, right = args[0], args[1]
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        if type(right) == int:
            right = BV(right, MAXINT)
        return BVULT(left, right)

    def LessEq(self, modulename, el, args):
        left, right = args[0], args[1]
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        if type(right) == int:
            right = BV(right, MAXINT)
        return BVULE(left, right)
    
    def GreaterThan(self, modulename, el, args):
        left, right = args[0], args[1]
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
        
        if type(right) == int:
            right = BV(right, MAXINT)
        return BVUGT(left, right)

    def GreaterEq(self, modulename, el, args):
        left, right = args[0], args[1]
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
        
        if type(right) == int:
            right = BV(right, MAXINT)
        return BVUGE(left, right)
    
    def Ulnot(self, modulename, el, args):
        if type(args[0]) == int:
            return Not(self.to_bool(args[0]))
        zero = BV(0, args[0].symbol_type().width)
        return EqualsOrIff(args[0], zero)

    def Unot(self, modulename, el, args):
        return self.Ulnot(modulename, el, args)
    
    def Parameter(self, modulename, el, args):
        if el.name not in self.paramdic:
            self.paramdic[el.name] = args[0]
        return None

    def SystemCall(self, modulename, el, args):
        if el.syscall == "clog2":
            return math.ceil(math.log(args[0])/math.log(2))

        Logger.error("Unimplemented system call \"%s\", line %d"%(el.syscall, el.lineno))
        
    def Partselect(self, modulename, el, args):
        if abs(args[1]-args[2])+1 == get_type(args[0]).width:
            return args[0]
        return BVExtract(args[0], args[2], args[1])

    def Assign(self, modulename, el, args):
        left, right = args[0], args[1]

        if type(right) == int:
            right = BV(right, get_type(left).width)
        
        invar = EqualsOrIff(B2BV(left), B2BV(right))
        self.ts.invar = And(self.ts.invar, invar)
        return el
    
    def Pointer(self, modulename, el, args):
        if type(args[0]) == tuple:
            width = get_type(args[1]).width
            mem_size = args[0][1]
            mem_locations = ["%s_%d"%(args[0][0], i) for i in range(mem_size[0], mem_size[1]+1)]
            return mem_access(args[1], [self.varmap[v] for v in mem_locations], width)

        if (type(args[0]) == FNode) and (type(args[1]) == FNode):
            width_mem = get_type(args[0]).width
            width_idx = get_type(args[1]).width
            mem_locations = [BVExtract(args[0], i, i) for i in range(width_mem)]
            return mem_access(args[1], mem_locations, width_idx)

        # Management of memory access
        if (type(args[0]) == list) and (type(args[1]) == FNode):
            width_mem = len(args[0])
            width_idx = get_type(args[1]).width
            mem_locations = args[0]
            return mem_access(args[1], mem_locations, width_idx)

        if (type(args[0]) == list) and (type(args[1]) == int):
            return args[0][args[1]]
        
        return BVExtract(args[0], args[1], args[1])

    def Concat(self, modulename, el, args):
        if len(args) == 1:
            return args[0]
        return BVConcat(args[0], args[1])

    def _rec_repeat(self, el, count):
        if count == 1:
            return el
        return simplify(BVConcat(el, self._rec_repeat(el, count-1)))
    
    def Repeat(self, modulename, el, args):
        return self._rec_repeat(args[0], args[1])
    
    def PortArg(self, modulename, el, args):
        return (el.portname, args[0])

    def Instance(self, modulename, el, args):
        el_child = el.children()
        paramargs_idx = [el_child.index(p) for p in el_child if type(p) == ParamArg]
        portargs_idx = [el_child.index(p) for p in el_child if type(p) == PortArg]
        width_idx = [el_child.index(p) for p in el_child if type(p) == Width]

        portargs = [args[i] for i in portargs_idx]
        portargs.sort()
        paramargs = [args[i] for i in paramargs_idx]
        paramargs.sort()
        width = args[width_idx[0]] if len(width_idx) > 0 else None

        if el.module not in self.modulesdic:
            Logger.error("Module definition \"%s\" not found, line %d"%(el.module, el.lineno))
        
        param_modulename = el.module

        include_varargs = False
        varmap = {}
        
        parameterized_type = ["%s%s"%(p[0], p[1]) for p in paramargs]

        if include_varargs:
            parameterized_type += ["%s%s"%(p[0], get_type(p[1]).width) for p in portargs]
            for portarg in portargs:
                varmap[portarg[0]] = (get_type(portarg[1]).width, None)

        if len(parameterized_type) > 0:
            param_modulename = "%s__|%s|"%(param_modulename, ",".join(parameterized_type))

        instances = []

        # Management of multi instances e.g., type instance[k:0] (clk, input[k:0])
        if len(width_idx) > 0:
            formal_args = [p[0] for p in portargs]
            args_width_idx = [formal_args.index(c.portname) for c in el_child if type(c.children()[0]) == Partselect]
            map_ports = dict([(dict(portargs)[c.portname], dict(portargs)[c.portname].args()[0]) for c in el_child if type(c.children()[0]) == Partselect and dict(portargs)[c.portname].is_bv_extract()])
            remap_ports = [(p[0], map_ports[p[1]] if p[1] in map_ports else p[1]) for p in portargs]

            extract_port = lambda p,i: BVExtract(p, i, i)
            
            for i in range(args[width_idx[0]]):
                idx_params = [(p[0], extract_port(p[1], i) if remap_ports.index(p) in args_width_idx else p[1]) for p in remap_ports]
                idx_instance_name = "%s_%d"%(el.name, i)
                instances.append((idx_instance_name, idx_params))
        else:        
            instances = [(el.name, portargs)]

        for (instance, actualargs) in instances:
            instancewalker = VerilogSTSWalker()
            instancewalker.config = self.config
            instancewalker.paramdic = dict(paramargs)
            instancewalker.varmap = varmap
            instancewalker.modulesdic = self.modulesdic
            subhts = instancewalker.walk_module(self.modulesdic[el.module], param_modulename)
            subhts.name = param_modulename

            self.hts.add_sub(instance, subhts, tuple([a[1] for a in actualargs]))
        return args

    def InstanceList(self, modulename, el, args):
        return args

    def ParamArg(self, modulename, el, args):
        return (el.paramname, args[0])

    def StringConst(self, modulename, el, args):
        return el.value

    def Localparam(self, modulename, el, args):
        return self.Parameter(modulename, el, args)

    def GenerateStatement(self, modulename, el, args):
        return args

    def Length(self, modulename, el, args):
        return args

    def RegArray(self, modulename, el, args):
        return args

    def IdentifierScope(self, modulename, el, args):
        return el
    
    def IdentifierScopeLabel(self, modulename, el, args):
        Logger.error("Unsupported indentifier scope, line %d"%(el.lineno))
        return el

    def DelayStatement(self, modulename, el, args):
        delay = int(el.delay.value)
        if delay == 1:
            return delay
        Logger.error("Unsupported delay statement != 1, line %d"%(el.lineno))
        return el

    def ForeverStatement(self, modulename, el, args):
        statement = And(args)
        for el in [And(a) for a in args]:
            self.add_constraint(el)
        return TRUE()
