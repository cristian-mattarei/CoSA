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
import shutil
import copy

VPARSER = True

try:
    from pyverilog.vparser.parser import VerilogParser, VerilogPreprocessor
    from pyverilog.vparser.ply.yacc import yacc
    from pyverilog.vparser.lexer import VerilogLexer
    from pyverilog.vparser.plyparser import ParseError
    from pyverilog.vparser.ast import *
except:
    VPARSER = False

from pysmt.shortcuts import Symbol, BV, simplify, TRUE, FALSE, get_type, get_model, is_sat, is_unsat
from pysmt.shortcuts import And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, \
    BVExtract, BVAdd, BVSub, BVUDiv, BVConcat, BVULT, BVULE, BVUGT, BVUGE, BVXor, BVOr, BVLShl, BVZero, BVMul, BVNot
from pysmt.fnode import FNode
from pysmt.typing import BOOL, BVType, ArrayType, INT
from pysmt.rewritings import conjunctive_partition
from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.walkers import TreeWalker
from pysmt.walkers.dag import DagWalker

from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser, ModelInformation
from cosa.encoders.modules import Modules
from cosa.walkers.verilog_walker import VerilogWalker
from cosa.representation import HTS, TS
from cosa.utils.generic import bin_to_dec, dec_to_bin, suppress_output, restore_output
from cosa.utils.formula_mngm import B2BV, BV2B, get_free_variables, substitute, mem_access
from cosa.environment import Assign, Define, ASSIGN, DEFINE, Finally
from cosa.printers.template import HIDDEN_VAR

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

IVERILOG = "iverilog"

MAXINT = 64

POSEDGE = "posedge"
NEGEDGE = "negedge"
LEVEL = "level"
INPUT = "input"
OUTPUT = "output"
CLOCK = "clk"

MODPARST = "__|"
MODPAREN = "|"

# SystemVerilog Verific modules
SVA_POSEDGE = "sva_posedge"
SVA_AT = "sva_at"
SVA_ASSERT = "sva_assert"
SVA_IMMEDIATE_ASSERT = "sva_immediate_assert"

SV_MODULES = [SVA_POSEDGE, SVA_AT, SVA_ASSERT, SVA_IMMEDIATE_ASSERT]

ASSERT_ST = HIDDEN_VAR+"assert__l"
ASSERTI_ST = HIDDEN_VAR+"asserti__l"
ASSERT_EN = HIDDEN_VAR[::-1]
ASSERT_SYMBOL = ASSERT_ST+"%d"+ASSERT_EN
ASSERTI_SYMBOL = ASSERTI_ST+"%d"+ASSERT_EN

NODE_ST = HIDDEN_VAR
NODE_SYMBOL = NODE_ST+"%s"

DONTCARE_VAR = HIDDEN_VAR+"value_%s"

class VerilogHTSParser(ModelParser):
    parser = None
    extensions = ["v"]
    name = "Verilog"

    files_from_dir = False
    
    def __init__(self):
        self.walker = VerilogSTSWalker()

    def get_model_info(self):
        model_info = ModelInformation()
        model_info.abstract_clock_list = self.abstract_clock_list
        model_info.clock_list = self.clock_list
        return model_info
    
    def is_available(self):
        return VPARSER and shutil.which(IVERILOG) is not None
    
    def parse_file(self, strfile, config, flags=None):
        invar_props = []
        ltl_props = []

        if flags is None:
            Logger.error("Module name not provided")
        
        absstrfile = os.path.abspath(strfile)

        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()

        ast = self.parse([absstrfile])

        if not Logger.level(print_level):
            restore_output(saved_stdout)

        if Logger.level(2):
            timer = Logger.start_timer("encoding")

        self.walker.config = config
        hts = self.walker.walk(ast, flags[0])
        self.abstract_clock_list = self.walker.abstract_clock_list
        self.clock_list = self.walker.clock_list

        if Logger.level(2):
            Logger.get_timer(timer)
            timer = Logger.start_timer("flattening")
        
        hts.flatten()

        if Logger.level(2):
            Logger.get_timer(timer)

        if config.zero_init:
            ts = TS("zero-init")
            assigns = []
            for var in hts.state_vars:
                if var.symbol_type().is_bv_type():
                    assigns.append(EqualsOrIff(var, BVZero(var.bv_width())))
                if var.symbol_type().is_bool_type():
                    assigns.append(Not(var))
            ts.init = And(assigns)
            hts.add_ts(ts)

        invar_props, ltl_props = self.__extract_properties(hts, strfile)

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

    def __extract_properties(self, hts, strfile):
        assertvars = [v.symbol_name() for v in hts.vars if ASSERT_ST in v.symbol_name() or ASSERTI_ST in v.symbol_name()]

        invar_props = []
        ltl_props = []

        print_line = False

        # If the assertion line has a comment in the format // <filename>(lineno)
        # it reports the line in the comment
        def extract_lineno(line, linenum):
            orig_lineno = re.search("/\w.*\(\d+\)", line)
            if orig_lineno is None:
                return line, linenum

            strfile, linenum = re.search("/\w.*\(", line), re.search("\(\d+\)", line)
            if (strfile is None) or (linenum is None):
                return line, linenum
            
            strfile = strfile.group(0)[:-1]
            linenum = int(linenum.group(0)[1:-1])

            if print_line:
                with open(strfile, "r") as f:
                    line = f.readlines()[linenum-1]

            return line, linenum
            
        
        if len(assertvars) > 0:
            with open(strfile, "r") as f:
                lines = f.readlines()
            
            for assertion in assertvars:
                asserti = ASSERTI_ST in assertion
                prefix = ASSERTI_ST if asserti else ASSERT_ST
                linenum = int(assertion[assertion.find(prefix)+len(prefix):assertion.find(ASSERT_EN)])
                line, linenum = extract_lineno(lines[linenum-1], linenum)
                line = re.sub(' +',' ',line.strip())

                lineprint = ", \"%s\""%line if print_line else ""
                
                if asserti:
                    ltl_props.append(("ImmediateAssertion_line_%d"%linenum, "Immediate assertion at line %d%s"%(linenum, lineprint), "F(%s)"%assertion))
                else:
                    invar_props.append(("Assertion_line_%d"%linenum, "Assertion at line %d%s"%(linenum, lineprint), assertion))

        return invar_props, ltl_props

class SpecVerilogParser(VerilogParser):

    def __init__(self):
        self.lexer = VerilogLexer(error_func=self._lexer_error_func)
        self.lexer.build()

        self.tokens = self.lexer.tokens
        self.parser = yacc(module=self, method="LALR", outputdir="/tmp/", debug=False)
    
class VerilogCodeParser(object):

    def __init__(self, filelist, preprocess_output='preprocess.output',
                 preprocess_include=None,
                 preprocess_define=None):
        self.preprocess_output = preprocess_output
        self.directives = ()
        self.preprocessor = VerilogPreprocessor(filelist, preprocess_output,
                                                preprocess_include,
                                                preprocess_define)
        prev_path = sys.path
        self.parser = SpecVerilogParser()
        sys.path = prev_path

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

    reglist = None
    outputlist = None
    memlist = None
    mod_map = None
    
    id_vars = 0

    abstract_clock_list = None
    clock_list = None

    hide_autogenerated = True
    
    def __init__(self):
        self.reset_structures()

    def reset_structures(self, modulename=""):
        self.hts = HTS(modulename)
        self.ts = TS()
        self.portslist = None
        self.reglist = []
        self.outputlist = []
        self.memlist = []
        self.abstract_clock_list = []
        self.clock_list = []
        if self.varmap is None: self.varmap = {}
        if self.paramdic is None: self.paramdic = {}
        if self.modulesdic is None: self.modulesdic = {}
        self._init_mod_map()
        
    def _fresh_symbol(self, name):
        VerilogSTSWalker.id_vars += 1
        return "%s__%d"%(name, VerilogSTSWalker.id_vars)

    def assign_define_substitute(self, formula):
        subwalker = AssignDefineSubstituteWalker()
        subwalker.reset()
        ret = subwalker.walk(formula)
        return (ret, list(subwalker.assign_list))

    def is_autogenerated(self, name):
        if re.match("n\d+", name) is not None:
            return True

        if re.match("Select_\d+", name) is not None:
            return True

        if re.match("LessThan_\d+u_\d+u", name) is not None:
            return True

        if re.match("add_\d+u_\d+u", name) is not None:
            return True

        if re.match("mult_\d+s_\d+s", name) is not None:
            return True
        
        if name == "VERIFIC_DLATCHRS":
            return True

        return False
    
    def add_init(self, constraint):
        self.ts.init = And(self.ts.init, self.assign_define_substitute(constraint)[0])

    def add_invar(self, constraint):
        self.ts.invar = And(self.ts.invar, self.assign_define_substitute(constraint)[0])

    def add_trans(self, constraint):
        self.ts.trans = And(self.ts.trans, self.assign_define_substitute(constraint)[0])
        
    def add_constraint(self, constraint):
        if TS.has_next(constraint):
            self.add_trans(constraint)
        else:
            self.add_invar(constraint)

    def add_ftrans(self, variable, cond_assign_list):
        self.ts.add_func_trans(variable, cond_assign_list)

    def clean_name(self, name):
        if name[0] == "\\":
            return name[1:]
        return name
            
    def varname(self, modulename, varname):
        varname = self.clean_name(varname)
        if modulename == "":
            return varname
        return "%s.%s"%(modulename, varname)

    def _add_clock_behavior(self, var, modulename):
        varname = var.symbol_name()
        if (CLOCK in varname):
            self.clock_list.append(var)

    def _init_mod_map(self):
        mod_map = []
        mod_map.append(("and",  Modules.And_M))
        mod_map.append(("nand",  Modules.Nand_M))
        mod_map.append(("or",   Modules.Or_M))
        mod_map.append(("nor",  Modules.Nor_M))
        mod_map.append(("not",  Modules.Not_M))
        mod_map.append(("xor",  Modules.Xor_M))

        self.mod_map = dict(mod_map)
            
    def Paramlist(self, modulename, el, args):
        return el

    def Wire(self, modulename, el, args):
        elname = el.name

        if self.hide_autogenerated:
            if self.is_autogenerated(el.name):
                elname = NODE_SYMBOL%elname

        width = args[0] if args is not None else 1
        wvar = Symbol(self.varname(modulename, elname), BVType(width))
        self.add_var(modulename, elname, wvar)
        self.ts.add_var(wvar)
        return (elname, args)

    def Reg(self, modulename, el, args):
        width = args[0] if args is not None else 1
        symbol = Symbol(self.varname(modulename, el.name), BVType(width))
        self.add_var(modulename, el.name, symbol)
        self.reglist.append(symbol)
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
                    self._add_clock_behavior(var, modulename)
                continue
            
            if type(porttype) == Output:
                if portsize is None:
                    self.add_var(modulename, portname, (None, OUTPUT))
                else:
                    width = portsize[0]
                    var = Symbol(self.varname(modulename, portname), BVType(width))
                    self.add_var(modulename, portname, var)
                    self.ts.add_output_var(var)
                    self.outputlist.append(var)
                continue

            if type(porttype) == Input:
                if portsize is None:
                    self.add_var(modulename, portname, (None, INPUT))
                else:
                    width = portsize[0]
                    var = Symbol(self.varname(modulename, portname), BVType(width))
                    self.add_var(modulename, portname, var)
                    self.ts.add_input_var(var)
                    self._add_clock_behavior(var, modulename)
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
                self._add_clock_behavior(var, modulename)
            if self.varmap[varname][1] == OUTPUT:
                self.ts.add_output_var(var)
                self.outputlist.append(var)
            self.varmap[varname] = var
            return var
        else:
            return self.varmap[varname]
        
    def Decl(self, modulename, el, args):
        if args[0] == None:
            return None

        direction = el.children()[0]

        if type(direction) in [Input, Output, Inout, Reg, Wire]:
            width = args[0][1]
            typ = el.children()[0]
            typname = typ.name

            if self.hide_autogenerated:
                typname = args[0][0]
            
            if width is None:
                if typname not in self.varmap:
                    Logger.error("Variable \"%s\" not defined, line %d"%(typname, el.lineno))
                var_inmap = self.varmap[typname]
                if type(var_inmap) == tuple:
                    width = 1 if var_inmap[0] is None else var_inmap[0]
                else:
                    width = var_inmap.symbol_type().width
            else:
                width = width[0]
            
            if typname in self.varmap:
                prev_width = self.varmap[typname][0] if type(self.varmap[typname]) is not FNode else self.varmap[typname].symbol_type().width
                if (prev_width is not None) and (prev_width != width):
                    Logger.error("Unmatched variable size at line %d"%el.lineno)

            var = Symbol(self.varname(modulename, typname), BVType(width))

            if type(direction) == Input:
                self.ts.add_input_var(var)
                self._add_clock_behavior(var, modulename)
            elif type(direction) == Output:
                self.ts.add_output_var(var)
                self.outputlist.append(var)
            elif type(direction) == Reg:
                self.ts.add_state_var(var)
            else:
                self.ts.add_var(var)

            self.add_var(modulename, typname, var)

            return None

        if type(direction) == RegArray:
            low, high = args[0][1][1], args[0][1][0]
            low, high = min(low, high), max(low, high)
            width = args[0][0]
            vname = el.children()[0].name
            var_idxs = []
            for i in range(low, high+1, 1):
                vname_idx = self.get_num_name(vname, i, high)
                var_idx = Symbol(self.varname(modulename, vname_idx), BVType(width))
                var_idxs.append(var_idx)
                self.add_var(modulename, vname_idx, var_idx)
                self.ts.add_state_var(var_idx)
                self.memlist.append(var_idx)

            self.add_var(modulename, vname, var_idxs)
            self.ts.add_hidden_var(Symbol(self.varname(modulename, vname), BVType(width)))
                
            return None
        
        Logger.error("Unmanaged type %s, line %d"%(type(direction), el.lineno))

    def get_num_name(self, name, idx, maxval):
        return "%s_%s"%(name, str(idx).rjust(len(str(maxval)),"0"))
        
    def Sens(self, modulename, el, args):
        if el.sig is None:
            return TRUE()
            
        var = self.get_var(modulename, el.sig.name)

        zero = BV(0, var.symbol_type().width)
        one = BV(1, var.symbol_type().width)

        if el.type == POSEDGE:
            if self.config.abstract_clock:
                self.abstract_clock_list.append((var, (zero, one)))
                return EqualsOrIff(var, one)
            return And(EqualsOrIff(TS.get_prime(var), one), EqualsOrIff(var, zero))

        if el.type == NEGEDGE:
            if self.config.abstract_clock:
                Logger.warning("Clock abstraction activated with negedge behavior")
                self.abstract_clock_list.append((var, (one, zero)))
                return EqualsOrIff(var, zero)

            return And(EqualsOrIff(TS.get_prime(var), zero), EqualsOrIff(var, one))

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
            
        return Assign(left, right)

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
            
        return Define(left, B2BV(right))

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

            if (type(value) == str) and ("x" in value):
                if width == "":
                    Logger.error("Non deterministic value definition requires size, line %d"%el.lineno)

                valname = DONTCARE_VAR%value
                valvar = Symbol(self.varname(modulename, valname), BVType(int(width)))
                self.add_var(modulename, valname, valvar)
                self.ts.add_var(valvar)
                # Inverting the value, e.g., with 'b1x x is the least significant
                value = value[::-1]
                if len(value) > 1:
                    valconstr = TRUE()
                    for val in value:
                        if val == "x":
                            continue
                        index = value.index(val)
                        invalue = BV(0,1) if int(val) == 0 else BV(1,1)
                        valconstr = And(valconstr, EqualsOrIff(BVExtract(valvar, index, index), invalue))
                    self.add_constraint(valconstr)
                return valvar

            return BV(int(bin_to_dec(value)), int(width))
        
        return int(el.value)

    def Identifier(self, modulename, el, args):
        elname = el.name

        if self.hide_autogenerated:        
            if self.is_autogenerated(elname):
                elname = NODE_SYMBOL%elname
        
        if elname in self.paramdic:
            return self.paramdic[elname]

        if elname in self.varmap:
            return self.get_var(modulename, elname)

        Logger.error("Symbol \"%s\" is not defined, line %d"%(elname, el.lineno))
        return elname
    
    def Width(self, modulename, el, args):
        return (args[0] - args[1])+1
    
    def Block(self, modulename, el, args):
        return [a for a in args if a is not None]

    def Cond(self, modulename, el, args):
        if args[0] in [False, FALSE()]:
            return args[2]
        if args[0] in [True, TRUE()]:
            return args[1]
        return Ite(BV2B(args[0]), args[1], args[2])
    
    def IfStatement(self, modulename, el, args):
        statement, then_b, else_b = args[0], args[1], args[2] if len(args) > 2 else None

        if type(then_b) == list:
            if len(then_b) == 0:
                then_b = None
            elif type(then_b[0]) == FNode:
                then_b = And(then_b)
            elif type(then_b[0]) == ProcessedAlways:
                pass
            else:
                Logger.error("Not Implemented")

        if type(else_b) == list:
            if len(else_b) == 0:
                else_b = None
            elif type(else_b[0]) == FNode:
                else_b = And(else_b)
            elif type(else_b[0]) == ProcessedAlways:
                pass
            else:
                Logger.error("Not Implemented")
                
        if type(statement) == int:
            condition = self.to_bool(statement)
        elif (type(statement) == bool) or (get_type(statement) == BOOL):
            condition = statement
        else:
            one = BV(1, get_type(statement).width)
            condition = EqualsOrIff(statement, one)

        if else_b is None:
            if then_b is None:
                return None
            if condition in [True, TRUE()]:
                return then_b
            if condition in [False, FALSE()]:
                return None
            return Implies(condition, then_b)
        else:
            if condition in [True, TRUE()]:
                assert (then_b is not None)
                return then_b
            if condition in [False, FALSE()]:
                assert (else_b is not None)
                return else_b
            assert (then_b is not None) and (else_b is not None)
            return Ite(condition, then_b, else_b)

    def Initial(self, modulename, el, args):
        self.add_init(And([And(a) for a in args]))
        return And(args)

    def process_always(self, modulename, always_list):
        if len(always_list) == 0:
            return

        g_always = {}

        # Combine all conditions
        for always in always_list:
            for v in always:
                if v not in g_always:
                    g_always[v] = []
                g_always[v] += always[v]

        state_vars = set(self.reglist+self.memlist)
        possible_ass_vars = set(self.reglist+self.outputlist+self.memlist)
        ass_vars = set(g_always.keys())
        diff_vars = ass_vars.difference(possible_ass_vars)

        strip_name = modulename[:modulename.find(MODPARST)] if MODPARST in modulename else modulename
        
        if len(diff_vars) > 0:
            Logger.error("Assignment is not allowed to variables \"%s\" in module \"%s\""%(", ".join([v.symbol_name().replace("%s."%(modulename),"") for v in diff_vars]), strip_name))

        ftrans = {}

        for var in possible_ass_vars:
            keep_value = EqualsOrIff(var, TS.get_prime(var))
            if (var not in g_always):
                if (var in state_vars):
                    self.add_constraint(keep_value)
                continue

            for beh in g_always[var]:
                effect, condition = self.assign_define_substitute(beh[0])[0], beh[1]
                condition = simplify(condition)

                # assignment and value from the assign operator (this can differ from var with the addition of bitvector extraction)
                avar, aval = beh[0].args()[0], beh[0].args()[1]
                # Only assignments to primed variables are added to the functional transition relation
                cons = simplify(Implies(condition, effect))

                if avar not in ftrans:
                    ftrans[avar] = []
                ftrans[avar].append((condition, aval))

        # Sort and simplifies assignments in case of ITE encoding
        sort_assignments = False
        
        for var, asscond in ftrans.items():
            if not sort_assignments:
                self.add_ftrans(var, asscond)
            else:
                sim_asscond = [(len(list(conjunctive_partition(x[0]))), str(x[1]), list(conjunctive_partition(x[0])), x[1]) for x in asscond]
                sim_asscond.sort()
                cum_cond = []
                new_assconds = []
                for el in sim_asscond:
                    cp_cond, value = el[2], el[3]
                    new_asscond = And([x for x in cp_cond if x not in cum_cond])
                    cum_cond += [Not(x) for x in cp_cond]
                    new_assconds.append((new_asscond, value))
                self.add_ftrans(var, new_assconds)

    # Simplifies ites according with a provided condition
    def simplify_ites(self, formula, condition):
        subwalker = IteSubstituteWalker()
        subwalker.set_condition(condition)
        return subwalker.walk(formula)
            
    def Always(self, modulename, el, args):
        condition, statements = args[0], args[1]

        if type(statements) == FNode:
            statements = [statements]

        if And(statements) == TRUE():
            return TRUE()
            
        # All variables in the senselist are accessed at the primed time
        sensedict = dict([(v.symbol_name(), TS.get_prime(v).symbol_name()) \
                          for v in get_free_variables(condition) if not TS.is_prime(v)])
        
        for i in range(len(statements)):
            statements[i] = substitute(statements[i], sensedict)

        assign_conditions = self.collect_assign_conditions(And(statements))

        # The variable assignments apply only when the "always condition" is true
        for v in assign_conditions:
            for i in range(len(assign_conditions[v])):
                avalue, acond = assign_conditions[v][i][0], assign_conditions[v][i][1]
                avalue = self.simplify_ites(avalue, acond)
                assign_conditions[v][i] = (avalue, And(acond, condition))
            
        # Assignlist is a list of (variable, list((value, condition))), meaning that
        # the "variable" is assigned to "value" when "condition" is true
                
        # The result is the processed by the process_always function
        return ProcessedAlways(assign_conditions)
    
    def ForStatement(self, modulename, el, args):

        # Refining definition in primed format e.g., for(i=0;i<10;i=i+1) into for(i'=0;i<10;i'=i+1)
        args[0] = args[0].substitute(dict([(v, TS.get_prime(v)) for v in get_free_variables(args[0])]))
        cp = list(conjunctive_partition(args[2]))
        newcp = []
        for ass in cp:
            left, right = ass.args()[0], ass.args()[1]
            assert (ass.is_equals() or ass.is_iff() or \
                    ass.node_type() == ASSIGN or \
                    ass.node_type() == DEFINE) and \
                    (left.is_symbol() or right.is_symbol())
            if left.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(left), right))
            if right.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(right), left))

        args[2] = And(newcp)

        args_0 = self.assign_define_substitute(args[0])[0]
        args_1 = self.assign_define_substitute(args[1])[0]
        args_2 = self.assign_define_substitute(args[2])[0]
        
        # Performining the For-loop unrolling
        fv = get_free_variables(args_0)
        model = get_model(args_0)
        state_n = [(v, model[v]) for v in fv]
        state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
        state = dict(state_c + state_n)
        formulae = []
        while True:
            # Evaluate new instance
            formula = simplify(And(args[3]).substitute(state))
            formulae.append(formula)

            # Compute next step
            model = get_model(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args_2))
            state_n = [(v, model[v]) for v in fv]
            state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
            state = dict(state_c + state_n)

            # Exit condition
            if not is_sat(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args_1)):
                break

        return And(formulae)

    def ModuleDef(self, modulename, el, args):
        always_list = [a.assign_conditions for a in args if type(a) == ProcessedAlways]
        for a in args:
            if (type(a) == list) and (len(a) > 0) and (type(a[0]) == ProcessedAlways):
                always_list += [x.assign_conditions for x in a]
        self.process_always(modulename, always_list)

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

    def Divide(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return int(left/right)
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
            
        if (type(right) == int):
            right = BV(right, MAXINT)

        if (type(left) == int):
            left = BV(left, MAXINT)
            
        return BVUDiv(left, right)

    def Uminus(self, modulename, el, args):
        return self.Minus(modulename, el, [0, args[0]])
    
    def Minus(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return left-right
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
            
        if (type(right) == int):
            right = BV(right, MAXINT)

        if (type(left) == int):
            left = BV(left, MAXINT)
            
        return BVSub(left, right)

    def Plus(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return left+right
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
            
        if (type(right) == int):
            right = BV(right, MAXINT)

        if (type(left) == int):
            left = BV(left, MAXINT)

        lft_width = get_type(left).width
        rgt_width = get_type(right).width

        if lft_width != rgt_width:
            if lft_width < rgt_width:
                left = BVConcat(BV(0, rgt_width-lft_width), left)
            if lft_width > rgt_width:
                right = BVConcat(BV(0, lft_width-rgt_width), right)

        return BVAdd(left, right)

    def Times(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return left*right
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
            
        if (type(right) == int):
            right = BV(right, MAXINT)

        if (type(left) == int):
            left = BV(left, MAXINT)

        return BVMul(left, right)
    
    def Eq(self, modulename, el, args):
        left, right = args[0], args[1]
        
        if left == right:
            return TRUE()

        if (type(left) == int) and (type(right) == int):
            return left==right        
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
        
        return EqualsOrIff(left, right)

    def Eql(self, modulename, el, args):
        return self.Eq(modulename, el, args)
    
    def NotEq(self, modulename, el, args):
        return Not(self.Eq(modulename, el, args))

    def NotEql(self, modulename, el, args):
        return self.NotEq(modulename, el, args)
    
    def to_bool(self, el):
        if type(el) == int:
            return FALSE() if el == 0 else TRUE()
        if type(el) == bool:
            return TRUE() if el else FALSE()
        return BV2B(el)

    def to_bv(self, el):
        if type(el) == int:
            return BV(el, 1)
        return B2BV(el)

    def Concat(self, modulename, el, args):
        return self._multi_op(BVConcat, args)
    
    def And(self, modulename, el, args):
        assert len(args) == 2
        return BVAnd(self.to_bv(args[0]), self.to_bv(args[1]))
    
    def Xor(self, modulename, el, args):
        assert len(args) == 2
        return BVXor(self.to_bv(args[0]), self.to_bv(args[1]))

    def Or(self, modulename, el, args):
        assert len(args) == 2
        return BVOr(self.to_bv(args[0]), self.to_bv(args[1]))

    def Uor(self, modulename, el, args):
        assert len(args) == 1
        # Or reduce
        zero = BV(0, get_type(args[0]).width)
        return Ite(EqualsOrIff(args[0], zero), BV(0,1), BV(1,1))

    def Uand(self, modulename, el, args):
        assert len(args) == 1
        # And reduce
        width = get_type(args[0]).width
        ones = BV((2**width)-1, width)
        return Ite(EqualsOrIff(args[0], ones), BV(1,1), BV(0,1))


    def Land(self, modulename, el, args):
        if set([type(a) for a in args]) == set([bool]):
            ret = args[0]
            for a in args[1:]:
                ret = ret or a
            return ret
        return simplify(And([self.to_bool(x) for x in args]))
    
    def Lor(self, modulename, el, args):
        if set([type(a) for a in args]) == set([bool]):
            ret = args[0]
            for a in args[1:]:
                ret = ret or a
            return ret
        return simplify(Or([self.to_bool(x) for x in args]))
    
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

        if (left == None) or (right == None):
            return False
        
        if (type(left) == int) and (type(right) == int):
            return left < right
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        return BVULT(left, right)

    def LessEq(self, modulename, el, args):
        left, right = args[0], args[1]

        if (left == None) or (right == None):
            return False
        
        if (type(left) == int) and (type(right) == int):
            return left <= right
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        return BVULE(left, right)
    
    def GreaterThan(self, modulename, el, args):
        left, right = args[0], args[1]

        if (left == None) or (right == None):
            return False
        
        if (type(left) == int) and (type(right) == int):
            return left > right
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        return BVUGT(left, right)

    def GreaterEq(self, modulename, el, args):
        left, right = args[0], args[1]

        if (left == None) or (right == None):
            return False
        
        if (type(left) == int) and (type(right) == int):
            return left >= right
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        return BVUGE(left, right)
    
    def Ulnot(self, modulename, el, args):
        return BVNot(args[0])

    def Unot(self, modulename, el, args):
        if type(args[0]) == int:
            return Not(self.to_bool(args[0]))
        zero = BV(0, get_type(args[0]).width)
        return EqualsOrIff(args[0], zero)
    
    def Parameter(self, modulename, el, args):
        if el.name not in self.paramdic:
            self.paramdic[el.name] = args[0]
        return None

    def SingleStatement(self, modulename, el, args):
        return None
    
    def SystemCall(self, modulename, el, args):
        if el.syscall == "clog2":
            return math.ceil(math.log(args[0])/math.log(2))

        if el.syscall == "display":
            return None

        if el.syscall == "finish":
            return None

        if el.syscall == "time":
            return None
        
        Logger.error("Unimplemented system call \"%s\", line %d"%(el.syscall, el.lineno))
        
    def Partselect(self, modulename, el, args):
        if abs(args[1]-args[2])+1 == get_type(args[0]).width:
            return args[0]
        return BVExtract(args[0], args[2], args[1])

    def Assign(self, modulename, el, args):
        left, right = args[0], args[1]

        if type(right) == int:
            right = BV(right, get_type(left).width)

        if get_type(left).is_bv_type() and get_type(right).is_bv_type():
            
            lft_width = get_type(left).width
            rgt_width = get_type(right).width

            if lft_width == rgt_width + 1:
                fv = get_free_variables(right)
                right = right.substitute(dict([(v, BVConcat(BV(0, 1), v)) for v in fv]))

            lft_width = get_type(left).width
            rgt_width = get_type(right).width

            if lft_width > rgt_width:
                right = BVConcat(BV(0, lft_width-rgt_width), right)

        self.add_ftrans(B2BV(left), [(TRUE(), B2BV(right))])
        return el
    
    def Pointer(self, modulename, el, args):
        if type(args[0]) == tuple:
            width = get_type(args[1]).width
            mem_size = args[0][1]
            mem_locations = [self.get_num_name(args[0][0], i, mem_size[1]+1) for i in range(mem_size[0], mem_size[1]+1)]
            ma = mem_access(args[1], [self.varmap[v] for v in mem_locations], width)
            return ma

        if (type(args[0]) == FNode) and (type(args[1]) == FNode):
            width_mem = get_type(args[0]).width
            width_idx = get_type(args[1]).width
            mem_locations = [BVExtract(args[0], i, i) for i in range(width_mem)]
            ma = mem_access(args[1], mem_locations, width_idx)
            return ma

        # Management of memory access
        if (type(args[0]) == list) and (type(args[1]) == FNode):
            width_mem = len(args[0])
            width_idx = get_type(args[1]).width
            mem_locations = args[0]
            ma = mem_access(args[1], mem_locations, width_idx)
            return ma

        if (type(args[0]) == list) and (type(args[1]) == int):
            return args[0][args[1]]
        
        return BVExtract(args[0], args[1], args[1])

    def LConcat(self, modulename, el, args):
        if len(args) == 1:
            return args[0]
        assert len(args) == 2
        return BVConcat(args[0], args[1])
    
    def _rec_repeat(self, el, count):
        if count == 1:
            return el
        return simplify(BVConcat(el, self._rec_repeat(el, count-1)))

    def _multi_op(self, op, args):
        if len(args) == 1:
            return args[0]
        ret = op(args[0], args[1])
        if len(args) > 2:
            for el in args[2:]:
                ret = op(ret, el)
        return ret
    
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

        l_formalp = len(list([p[0] for p in portargs]))
        l_actualp = len(list([p[1] for p in portargs]))
        l_totalp = len(portargs)

        if len(set([l_formalp, l_actualp, l_totalp])) > 1:
            Logger.error("Number of arguments don't match module interface, line %d"%(el.lineno))

        if len([p[0] for p in portargs if p[0] is None]) == 0:
            portargs.sort()
        paramargs = [args[i] for i in paramargs_idx]
        paramargs.sort()
        width = args[width_idx[0]] if len(width_idx) > 0 else None

        if el.module in SV_MODULES:
            if el.module == SVA_ASSERT:
                sname = ASSERT_SYMBOL%el.lineno
                asymbol = Symbol(self.varname(modulename, sname), BOOL)
                self.add_var(modulename, sname, asymbol)
                self.ts.add_var(asymbol)
                self.add_constraint(EqualsOrIff(asymbol, And([BV2B(a[1]) for a in args])))
            if el.module == SVA_AT:
                out = dict(args)["o"]
                in0 = dict(args)["a0"]
                in1 = dict(args)["a1"]
                self.add_constraint(EqualsOrIff(Implies(BV2B(in0), BV2B(in1)), BV2B(out)))
            if el.module == SVA_POSEDGE:
                out = dict(args)["o"]
                in_ = dict(args)["i"]
                if self.config.abstract_clock:
                    self.add_constraint(EqualsOrIff(BV2B(out), EqualsOrIff(in_, BV(1, 1))))
                else:
                    self.add_constraint(EqualsOrIff(BV2B(TS.to_next(out)), And(EqualsOrIff(in_, BV(0, 1)), EqualsOrIff(TS.to_next(in_), BV(1, 1)))))
            if el.module == SVA_IMMEDIATE_ASSERT:
                sname = ASSERTI_SYMBOL%el.lineno
                asymbol = Symbol(self.varname(modulename, sname), BOOL)
                self.add_var(modulename, sname, asymbol)
                self.ts.add_var(asymbol)
                self.add_constraint(EqualsOrIff(asymbol, And([BV2B(a[1]) for a in args])))
                
            return args
        
        if el.module not in self.modulesdic:
            if el.module in self.mod_map:
                actual_args = [p[1] for p in portargs]
                ts = self.mod_map[el.module](actual_args[0], *(actual_args[1:]))
                self.hts.add_ts(ts)
                return args
            else:
                Logger.error("Module definition \"%s\" not found, line %d"%(el.module, el.lineno))
        
        param_modulename = self.clean_name(el.module)

        include_varargs = False
        varmap = {}
        
        parameterized_type = ["%s%s"%(p[0], p[1]) for p in paramargs]

        if include_varargs:
            parameterized_type += ["%s%s"%(p[0], get_type(p[1]).width) for p in portargs]
            for portarg in portargs:
                varmap[portarg[0]] = (get_type(portarg[1]).width, None)

        hide_sub_vars = False
                
        if self.hide_autogenerated:
            if self.is_autogenerated(param_modulename):
                hide_sub_vars = True
                
        if len(parameterized_type) > 0:
            param_modulename = "".join((param_modulename, MODPARST, ",".join(parameterized_type), MODPAREN))

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
                idx_instance_name = self.get_num_name(el.name, i, args[width_idx[0]])
                instances.append((idx_instance_name, idx_params))
        else:        
            instances = [(el.name, portargs)]

        for (instance, actualargs) in instances:
            instance = self.clean_name(instance)
            instancewalker = VerilogSTSWalker()
            instancewalker.config = copy.deepcopy(self.config)
            instancewalker.config.add_clock = False
            instancewalker.paramdic = dict(paramargs)
            instancewalker.varmap = varmap
            instancewalker.modulesdic = self.modulesdic
            subhts = instancewalker.walk_module(self.modulesdic[el.module], param_modulename)
            subhts.name = param_modulename
                
            # Setting parameters to value None in case they are not provided
            if len(subhts.params) != len(actualargs):
                dic_form = dict([(".".join(p.symbol_name().split(".")[1:]), p) for p in subhts.params])
                lst_actu = [str(a[0]) for a in actualargs]

                for par in dic_form:
                    if par not in lst_actu:
                        actualargs.append((par, None))
                actualargs.sort()

            if hide_sub_vars:
                subhts.apply_var_prefix(HIDDEN_VAR)

            actual_ptype = [get_type(a[1]) for a in actualargs if a[1] is not None]
            formal_ptype = [get_type(p) for p in subhts.params if actualargs[subhts.params.index(p)][1] is not None]
            if formal_ptype != actual_ptype:
                formal = ["%s:%s"%(".".join(p.symbol_name().split(".")[1:]), get_type(p)) for p in subhts.params]
                actual = ["%s:%s"%(a[0], get_type(a[1])) for a in actualargs]
                Logger.error("Parameters type error, line %d\nformal=\"%s\" \nactual=\"%s\""%(el.lineno, formal, actual))
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
        if len(args) == 1:
            return args[0]
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

    def collect_conditions_rec(self, formula, ext_function, assign_list=[], collected={}):

        if formula.is_ite():
            listlen = len(assign_list)
            condition, then_b, else_b = formula.args()[0], formula.args()[1], formula.args()[2]
            (assign_list, collected) = self.collect_conditions_rec(then_b, ext_function, \
                                                                   assign_list[:listlen]+[condition], collected)
            (assign_list, collected) = self.collect_conditions_rec(else_b, ext_function, \
                                                                   assign_list[:listlen]+[Not(condition)], collected)

        if formula.is_implies():
            condition, then_b = formula.args()[0], formula.args()[1]
            (assign_list, collected) = self.collect_conditions_rec(then_b, ext_function, \
                                                                   assign_list+[condition], collected)

        if formula.is_and():
            lstlen = len(assign_list)

            for arg in formula.args():
                (assign_list, collected) = self.collect_conditions_rec(arg, ext_function, assign_list[:lstlen], collected)

        (assign_list, collected) = ext_function(formula, assign_list, collected)

        return (assign_list, collected)

    def collect_assign_conditions(self, formula):

        # Reduces an assignment (var = 0) & (var != 1) & (var != 2) .. into (var = 0)
        def simplify_assign_list(assign_list):
            cp = list(conjunctive_partition(assign_list))
            equals = [f for f in cp if f.is_equals()]
            if len(equals) != 1:
                if cp[0].args():
                    # Managing condition where all assignments are negated
                    get_eq_val = lambda f: f.args()[0] if f.args()[0].is_bv_constant() else f.args()[1]
                    get_eq_var = lambda f: f.args()[0] if not f.args()[0].is_bv_constant() else f.args()[1]
                    values = [get_eq_val(f.args()[0]).constant_value() for f in cp]
                    if len(values) == len(range(max(values)+1)):
                        refvar = get_eq_var(cp[0].args()[0])
                        return BVUGT(refvar, BV(max(values), refvar.symbol_type().width))
                
                return assign_list

            refel = equals[0]
            left, right = refel.args()[0], refel.args()[1]
            pos_var = left if left.is_symbol() else right
            pos_val = right if left.is_symbol() else left
            
            ret = [refel]
            for neq in [f.args()[0] for f in cp if f.is_not()]:
                if not neq.is_equals():
                    return assign_list

                left, right = neq.args()[0], neq.args()[1]
                neg_var = left if left.is_symbol() else right
                neg_val = right if left.is_symbol() else left

                if not((pos_var == neg_var) & (pos_val != neg_val)):
                    ret.append(neq)

            return And(ret)

        # External function for collect_conditions_rec. Symbols collection
        def var_fun(formula, assign_list, collected):
            if formula.is_symbol():
                ref_var = TS.get_ref_var(formula)
                if ref_var not in collected:
                    collected[ref_var] = []
                collected[ref_var].append((formula, And(assign_list)))
            return (assign_list, collected)
        
        # External function for collect_conditions_rec. Assigns and Defines collection
        def assign_define_fun(formula, assign_list, collected):
            left = formula.args()[0]
            if formula.node_type() in [ASSIGN, DEFINE]:
                if not left.is_symbol():
                    fv = get_free_variables(left)
                    mem_vars = [TS.get_ref_var(v) for v in fv if TS.get_ref_var(v) in self.memlist]
                    idx_vars = [TS.get_ref_var(v) for v in fv if TS.get_ref_var(v) not in self.memlist]

                    if left.is_bv_extract():
                        left = left.args()[0]
                    
                    var_conditions = self.collect_conditions_rec(left, var_fun, assign_list=[], collected={})[1]

                    lstlen = len(assign_list)
                    for var, conditions in var_conditions.items():
                        for cond in conditions:
                            assign_list = assign_list[:lstlen]
                            newcond = And(cond[1])
                            newcond = simplify_assign_list(newcond)
                            assign_list.append(newcond)
                            if var not in collected:
                                collected[var] = []
                            collected[var].append((formula, And(assign_list)))
                else:
                    ref_var = TS.get_ref_var(left)
                    if ref_var not in collected:
                        collected[ref_var] = []
                    collected[ref_var].append((formula, And(assign_list)))

            return (assign_list, collected)

        (assign_list, collected) = self.collect_conditions_rec(formula, assign_define_fun, assign_list=[], collected={})
        
        return collected

class IteSubstituteWalker(IdentityDagWalker):

    condition = None

    def set_condition(self, condition):
        self.condition = condition

    def walk_ite(self, formula, args, **kwargs):
        if is_unsat(And(args[0], self.condition)):
            return args[2]

        if is_unsat(And(Not(args[0]), self.condition)):
            return args[1]

        return formula
        
class AssignDefineSubstituteWalker(IdentityDagWalker):

    assign_list = None

    def reset(self):
        self.assign_list = set([])
    
    def walk_assign(self, formula, args, **kwargs):
        for v in get_free_variables(args[0]):
            self.assign_list.add(v)
        return self.mgr.EqualsOrIff(args[0], args[1])

    def walk_define(self, formula, args, **kwargs):
        for v in get_free_variables(args[0]):
            self.assign_list.add(v)
        return self.mgr.EqualsOrIff(args[0], args[1])
    
class ProcessedAlways(object):
    def __init__(self, assign_conditions):
        self.assign_conditions = assign_conditions
