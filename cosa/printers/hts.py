# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import datetime
import random

from six.moves import cStringIO

from pysmt.printers import HRPrinter
from pysmt.walkers import TreeWalker
from pysmt.utils import quote
from pysmt.shortcuts import Symbol, simplify, TRUE, FALSE, BOOL, And
from pysmt.rewritings import conjunctive_partition

from cosa.representation import TS
from cosa.encoders.coreir import SEP
from cosa.utils.generic import dec_to_bin, dec_to_hex
from cosa.encoders.ltl import has_ltl_operators
from cosa.environment import ExtHRPrinter
from cosa.utils.formula_mngm import get_free_variables
from cosa.utils.generic import sort_system_variables

from cosa.printers.template import HTSPrinter, HTSPrinterType

NL = "\n"
VCD_SEP = "-"

# Variables starting with HIDDEN are not printed
HIDDEN = "_-_"

class SMVHTSPrinter(HTSPrinter):
    name = "SMV"
    description = "\tSMV format"
    TYPE = HTSPrinterType.SMV
    EXT  = ".smv"

    def __init__(self):
        HTSPrinter.__init__(self)
        self.write = self.stream.write

        printer = SMVPrinter(self.stream)
        self.printer = printer.printer

    def print_hts(self, hts, properties=None):
        self.write("MODULE main\n")

        if properties is not None:
            for strprop, prop, _ in properties:
                if has_ltl_operators(prop):
                    self.write("\nLTLSPEC ")
                else:
                    self.write("\nINVARSPEC ")
                self.printer(prop)
                self.write(";\n")

        if hts.assumptions is not None:
            self.write("\n-- ASSUMPTIONS\n")
            for assmp in hts.assumptions:
                self.write("INVAR ")
                self.printer(assmp)
                self.write(";\n")

        printed_vars = set([])
        self.__print_single_ts(hts.get_TS(), printed_vars)
        # for ts in hts.tss:
        #     printed_vars = self.__print_single_ts(ts, printed_vars)

        ret = self.stream.getvalue()
        self.stream.truncate(0)
        self.stream.seek(0)
        return ret

    def names(self, name):
        return "\"%s\""%name

    def __print_single_ts(self, ts, printed_vars):

        has_comment = len(ts.comment) > 0
        
        if has_comment:
            lenstr = len(ts.comment)+3

            self.write("\n%s\n"%("-"*lenstr))
            self.write("-- %s\n"%ts.comment)
            self.write("%s\n"%("-"*lenstr))

        locvars = [v for v in ts.vars if v not in printed_vars]

        for v in ts.vars:
            printed_vars.add(v)

        if locvars: self.write("\nVAR\n")
        for var in locvars:
            sname = self.names(var.symbol_name())
            if var.symbol_type() == BOOL:
                self.write("%s : boolean;\n"%(sname))
            else:
                self.write("%s : word[%s];\n"%(sname, var.symbol_type().width))

        sections = [((ts.init),"INIT"), ((ts.invar),"INVAR"), ((ts.trans),"TRANS")]

        for (formula, keyword) in sections:
            if formula not in [TRUE(), FALSE()]:
                self.write("\n%s\n"%keyword)
                cp = list(conjunctive_partition(formula))
                for i in range(len(cp)):
                    f = simplify(cp[i])
                    self.printer(f)
                    if i < len(cp)-1:
                        self.write(" &\n")
                self.write(";\n")

        if has_comment:
            self.write("\n%s\n"%("-"*lenstr))

        return printed_vars

class STSHTSPrinter(HTSPrinter):
    name = "STS"
    description = "\tSimple STS format"
    TYPE = HTSPrinterType.STS
    EXT  = ".ssts"

    simplify = False

    def __init__(self):
        HTSPrinter.__init__(self)
        self.write = self.stream.write
        self.simplify = False

        printer = STSPrinter(self.stream)
        self.printer = printer.printer

    def print_hts(self, hts, properties=None, ftrans=False):
        if hts.assumptions is not None:
            self.write("\n# ASSUMPTIONS\n")
            for assmp in hts.assumptions:
                self.write("INVAR ")
                self.printer(assmp)
                self.write(";\n")

        self.__print_single_ts(hts.get_TS(ftrans=ftrans), ftrans)

        ret = self.stream.getvalue()
        self.stream.truncate(0)
        self.stream.seek(0)
        return ret

    def names(self, name):
        return "'%s'"%name

    def _simplify_cp(self, cp):
        random.shuffle(cp)
        newcp = []
        last = False
        step = 3
        for i in range(0, len(cp)-(step-1), step):
            if i == len(cp)-step:
                last = True
            formula = simplify(And([cp[i+j] for j in range(step)]))
            newcp += list(conjunctive_partition(formula))

        if not last:
            for i in range(-1, -step, -1):
                newcp.append(cp[i])
        return newcp
    
    def __print_single_ts(self, ts, ftrans=False):

        has_comment = len(ts.comment) > 0
        
        if has_comment:
            lenstr = len(ts.comment)+3

            self.write("\n%s\n"%("-"*lenstr))
            self.write("# %s\n"%ts.comment)
            self.write("%s\n"%("-"*lenstr))

        sections = [("INPUT", ts.input_vars),\
                    ("OUTPUT", ts.output_vars),\
                    ("STATE", ts.state_vars),\
                    ("VAR", [x for x in ts.vars if x not in list(ts.state_vars)+list(ts.input_vars)+list(ts.output_vars)])]

        for (sname, vars) in sections:
            if len(vars) > 0: self.write("%s\n"%sname)
            varsort = sort_system_variables(vars)
            for var in varsort:
                sname = self.names(var.symbol_name())
                if var.symbol_type() == BOOL:
                    self.write("%s : Bool;\n"%(sname))
                else:
                    self.write("%s : BV(%s);\n"%(sname, var.symbol_type().width))
            self.write("\n")

        sections = [((ts.init),"INIT"), ((ts.invar),"INVAR"), ((ts.trans),"TRANS")]

        for (formula, keyword) in sections:
            if formula not in [TRUE(), FALSE()]:
                self.write("%s\n"%keyword)
                cp = list(conjunctive_partition(formula))
                if self.simplify:
                    cp = self._simplify_cp(cp)

                cp = [x for x in cp if x.is_equals()]+[x for x in cp if not x.is_equals()]
                for i in range(len(cp)):
                    f = cp[i]
                    if self.simplify:
                        f = simplify(f)
                    if f == TRUE():
                        continue
                    self.printer(f)
                    self.write(";\n")
                    if f == FALSE():
                        break
                self.write("\n")

        if ftrans:
            if ts.ftrans is not None:
                self.write("FUNC\n")
                for var, var_ass in ts.ftrans.items():
                    self.printer(var)
                    self.write(" :=")
                    for cond, value in var_ass:
                        self.write(" {")
                        self.printer(cond)
                        self.write(", ")
                        self.printer(value)
                        self.write("}")
                    self.write(";\n")
                
        if has_comment:
            self.write("\n%s\n"%("-"*lenstr))
    

class SMVPrinter(ExtHRPrinter):

    # Override walkers for SMV specific syntax

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("TRUE")
        else:
            self.write("FALSE")

    def walk_bv_constant(self, formula):
        self.write("0ud%d_%d" % (formula.bv_width(), formula.constant_value()))

    def walk_bv_zext(self, formula):
        self.write("extend ")
        self.write("( ")
        yield formula.arg(0)
        self.write(", %d)" % formula.bv_extend_step())

    def walk_bv_extract(self, formula):
        yield formula.arg(0)
        self.write("[%d:%d]" % (formula.bv_extract_end(),
                                formula.bv_extract_start()))

    def walk_bv_ashr(self, formula):
        self.write("(unsigned(signed(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(") >> ")
        yield args[-1]
        self.write("))")

    def walk_bv_ult(self, formula): return self.walk_nary(formula, " < ")

    def walk_bv_ule(self, formula): return self.walk_nary(formula, " <= ")
    
    def walk_symbol(self, formula):
        if TS.is_prime(formula):
            self.write("next(\"%s\")"%TS.get_ref_var(formula).symbol_name())
        else:
            self.write("\"%s\""%formula.symbol_name())

class STSPrinter(ExtHRPrinter):

    # Override walkers for STS specific syntax
    def walk_symbol(self, formula):
        if TS.is_prime(formula):
            self.write("next('%s')"%TS.get_ref_var(formula).symbol_name())
        else:
            self.write("'%s'"%formula.symbol_name())

    def walk_bv_ult(self, formula): return self.walk_nary(formula, " < ")
    def walk_bv_ule(self, formula): return self.walk_nary(formula, " <= ")
    def walk_bv_ugt(self, formula): return self.walk_nary(formula, " > ")
