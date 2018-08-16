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
from cosa.encoders.ltl import has_ltl_operators, HRLTLPrinter
from cosa.utils.formula_mngm import get_free_variables

NL = "\n"
VCD_SEP = "-"

# Variables starting with HIDDEN are not printed
HIDDEN = "_-_"

class NotRegisteredPrinterException(Exception):
    pass

class PrinterType(object):
    NONE = 0

    c_size = 10
    ####################

    SMV = 11
    STS = 12

    TRANSSYS = 20

    ####################

class PrintersFactory(object):
    printers = []
    default_printer = None

    # Additional printers should be registered here #
    @staticmethod
    def init_printers():
        PrintersFactory.register_printer(SMVHTSPrinter(), True)
        PrintersFactory.register_printer(STSHTSPrinter(), False)

    @staticmethod
    def get_default():
        return PrintersFactory.default_printer

    @staticmethod
    def register_printer(printer, default=False):
        if printer.get_name() not in dict(PrintersFactory.printers):
            PrintersFactory.printers.append((printer.get_name(), printer))
            if default:
                PrintersFactory.default_printer = printer

    @staticmethod
    def printer_by_name(name):
        PrintersFactory.init_printers()
        dprint = dict(PrintersFactory.printers)
        if name not in dprint:
            Logger.error("Printer \"%s\" is not registered"%name)
        return dprint[name]

    @staticmethod
    def get_printers():
        PrintersFactory.init_printers()
        return [x[0] for x in PrintersFactory.printers]

    @staticmethod
    def get_printers_by_type(printertype):
        PrintersFactory.init_printers()
        if (printertype % PrinterType.c_size) == 0:
            return [x[1] for x in PrintersFactory.printers \
                    if (x[1].TYPE < printertype) and (x[1].TYPE >= printertype-PrinterType.c_size)]

        return [x[1] for x in PrintersFactory.printers if x[1].TYPE == printertype]

class HTSPrinter(object):
    name = "PRINTER"
    description = "MISSING DESCRIPTION!"
    TYPE = PrinterType.NONE
    EXT  = ".none"

    def __init__(self):
        self.stream = cStringIO()

    def print_hts(self, hts):
        pass

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

class SMVHTSPrinter(HTSPrinter):
    name = "SMV"
    description = "\tSMV format"
    TYPE = PrinterType.SMV
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
        for ts in hts.tss:
            printed_vars = self.__print_single_hts(ts, printed_vars)

        ret = self.stream.getvalue()
        self.stream.truncate(0)
        self.stream.seek(0)
        return ret

    def names(self, name):
        return "\"%s\""%name

    def __print_single_hts(self, hts, printed_vars):

        has_comment = len(hts.comment) > 0
        
        if has_comment:
            lenstr = len(hts.comment)+3

            self.write("\n%s\n"%("-"*lenstr))
            self.write("-- %s\n"%hts.comment)
            self.write("%s\n"%("-"*lenstr))

        locvars = [v for v in hts.vars if v not in printed_vars]

        for v in hts.vars:
            printed_vars.add(v)

        if locvars: self.write("\nVAR\n")
        for var in locvars:
            sname = self.names(var.symbol_name())
            if var.symbol_type() == BOOL:
                self.write("%s : boolean;\n"%(sname))
            else:
                self.write("%s : word[%s];\n"%(sname, var.symbol_type().width))

        sections = [((hts.init),"INIT"), ((hts.invar),"INVAR"), ((hts.trans),"TRANS")]

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
    TYPE = PrinterType.STS
    EXT  = ".ssts"

    simplify = False

    def __init__(self):
        HTSPrinter.__init__(self)
        self.write = self.stream.write
        self.simplify = False

        printer = STSPrinter(self.stream)
        self.printer = printer.printer

    def print_hts(self, hts, properties=None):
        if hts.assumptions is not None:
            self.write("\n# ASSUMPTIONS\n")
            for assmp in hts.assumptions:
                self.write("INVAR ")
                self.printer(assmp)
                self.write(";\n")

        self.__print_single_ts(hts.get_TS())

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
    
    def __print_single_ts(self, ts):

        has_comment = len(ts.comment) > 0
        
        if has_comment:
            lenstr = len(ts.comment)+3

            self.write("\n%s\n"%("-"*lenstr))
            self.write("# %s\n"%ts.comment)
            self.write("%s\n"%("-"*lenstr))

        sections = [("VAR", [x for x in ts.vars if x not in list(ts.state_vars)+list(ts.input_vars)+list(ts.output_vars)]),\
                    ("STATE", ts.state_vars),\
                    ("INPUT", ts.input_vars),\
                    ("OUTPUT", ts.output_vars)]

        for (sname, vars) in sections:
            if len(vars) > 0: self.write("%s\n"%sname)
            for var in vars:
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
    
                for i in range(len(cp)):
                    f = simplify(cp[i])
                    if f == TRUE():
                        continue
                    self.printer(f)
                    self.write(";\n")
                    if f == FALSE():
                        break
                self.write("\n")
                    
        if has_comment:
            self.write("\n%s\n"%("-"*lenstr))
    

class SMVPrinter(HRLTLPrinter):

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

class STSPrinter(HRLTLPrinter):

    # Override walkers for STS specific syntax
    def walk_symbol(self, formula):
        if TS.is_prime(formula):
            self.write("next('%s')"%TS.get_ref_var(formula).symbol_name())
        else:
            self.write("'%s'"%formula.symbol_name())

    def walk_bv_ult(self, formula): return self.walk_nary(formula, " < ")
    def walk_bv_ule(self, formula): return self.walk_nary(formula, " <= ")
    def walk_bv_ugt(self, formula): return self.walk_nary(formula, " > ")
            

class TracePrinter(object):

    def __init__(self):
        pass

    def print_trace(self, hts, model, length, map_function=None):
        pass

    def get_file_ext(self):
        pass

    def is_hidden(self, name):
        return name[:len(HIDDEN)] == HIDDEN

class TextTracePrinter(TracePrinter):

    def __init__(self):
        self.extra_vars = None
        self.diff_only = True
        self.all_vars = False

    def get_file_ext(self):
        return ".txt"

    def print_trace(self, hts, modeldic, length, map_function=None, find_loop=False):
        trace = []
        prevass = []

        hex_values = False
        
        trace.append("---> INIT <---")

        if self.all_vars:
            varlist = list(hts.vars)
        else:
            varlist = list(hts.input_vars.union(hts.output_vars).union(hts.state_vars))
            if self.extra_vars is not None:
                varlist = list(set(varlist).union(set(self.extra_vars)))

        strvarlist = [(map_function(var.symbol_name()), var) for var in varlist if not self.is_hidden(var.symbol_name())]
        strvarlist.sort()

        for var in strvarlist:
            var_0 = TS.get_timed(var[1], 0)
            if var_0 not in modeldic:
                continue
            varass = (var[0], modeldic[var_0])
            if hex_values:
                varass = (varass[0], dec_to_hex(varass[1].constant_value(), int(var[1].symbol_type().width/4)))
            if self.diff_only: prevass.append(varass)
            trace.append("  I: %s = %s"%(varass[0], varass[1]))

        if self.diff_only: prevass = dict(prevass)

        for t in range(length):
            trace.append("\n---> STATE %s <---"%(t+1))

            for var in strvarlist:
                var_t = TS.get_timed(var[1], t+1)
                if var_t not in modeldic:
                    continue
                varass = (var[0], modeldic[var_t])
                if hex_values:
                    varass = (varass[0], dec_to_hex(varass[1].constant_value(), int(var[1].symbol_type().width/4)))
                if (not self.diff_only) or (prevass[varass[0]] != varass[1]):
                    trace.append("  S%s: %s = %s"%(t+1, varass[0], varass[1]))
                    if self.diff_only: prevass[varass[0]] = varass[1]

        if find_loop:
            last_state = [(var[0], modeldic[TS.get_timed(var[1], length)]) for var in strvarlist]
            last_state.sort()
            loop_id = -1
            for i in range(length):
                state_i = [(var[0], modeldic[TS.get_timed(var[1], i)]) for var in strvarlist]
                state_i.sort()
                if state_i == last_state:
                    loop_id = i
                    break
            if loop_id >= 0: 
                trace.append("\n---> STATE %s loop to STATE %s <---"%(length, loop_id))


        trace = NL.join(trace)
        return trace

class VCDTracePrinter(TracePrinter):

    def __init__(self):
        pass

    def get_file_ext(self):
        return ".vcd"

    def print_trace(self, hts, modeldic, length, map_function=None):
        hierarchical = False
        ret = []

        ret.append("$date")
        ret.append(datetime.datetime.now().strftime('%A %Y/%m/%d %H:%M:%S'))
        ret.append("$end")
        ret.append("$version")
        ret.append("CoSA")
        ret.append("$end")
        ret.append("$timescale")
        ret.append("1 ns")
        ret.append("$end")

        def _recover_array(store_ops):
            d = {}
            x = store_ops
            while len(x.args()) == 3:
                next_x, k, v = x.args()
                x = next_x
                if k.constant_value() not in d:
                    d[k.constant_value()] = v.constant_value()
            return d

        # TODO, use modeldic[v].array_value_assigned_values_map()
        # to get all the array values for a counterexample trace
        modeldic = dict([(v.symbol_name(), modeldic[v].constant_value()
                          if not v.symbol_type().is_array_type()
                          else _recover_array(modeldic[v])) for v in modeldic])

        # These are the pysmt array vars
        arr_vars = list(filter(lambda v: v.symbol_type().is_array_type(), hts.vars))

        # Figure out which indices are used over all time
        arr_used_indices = {}
        for av in arr_vars:
            name = av.symbol_name()
            indices = set()
            for t in range(length+1):
                tname = TS.get_timed_name(map_function(name), t)
                indices |= set((k for k in modeldic[tname]))
            arr_used_indices[name] = indices

        # These are the vcd vars (Arrays get blown out)
        varlist = []
        arr_varlist = []
        idvar = 0
        var2id = {}
        for v in list(hts.vars):
            n = map_function(v.symbol_name())
            if self.is_hidden(v.symbol_name()):
                continue
            if v.symbol_type() == BOOL:
                varlist.append((n, 1))
                var2id[n] = idvar
                idvar += 1
            elif v.symbol_type().is_bv_type():
                varlist.append((n, v.symbol_type().width))
                var2id[n] = idvar
                idvar += 1
            elif v.symbol_type().is_array_type():
                idxtype = v.symbol_type().index_type
                elemtype = v.symbol_type().elem_type
                for idx in arr_used_indices[n]:
                    indexed_name = n + "[%i]"%idx
                    arr_varlist.append((indexed_name, elemtype.width))
                    var2id[indexed_name] = idvar
                    idvar += 1
            else:
                Logger.error("Unhandled type in VCD printer")

        for el in varlist + arr_varlist:
            (varname, width) = el
            idvar = var2id[varname]

            if hierarchical:
                varname = varname.split(SEP)
                for scope in varname[:-1]:
                    ret.append("$scope module %s $end"%scope)

                ret.append("$var reg %d v%s %s[%d:0] $end"%(width, idvar, varname[-1], width-1))

                for scope in range(len(varname)-1):
                    ret.append("$upscope $end")
            else:
                varname = varname.replace(SEP, VCD_SEP)
                ret.append("$var reg %d v%s %s[%d:0] $end"%(width, idvar, varname, width-1))


        ret.append("$upscope $end")
        ret.append("$upscope $end")
        ret.append("$enddefinitions $end")

        for t in range(length+1):
            ret.append("#%d"%t)
            for el in varlist:
                (varname, width) = el
                tname = TS.get_timed_name(varname, t)
                val = modeldic[tname] if tname in modeldic else 0
                ret.append("b%s v%s"%(dec_to_bin(val, width), var2id[varname]))

            for a in arr_vars:
                name = a.symbol_name()
                width = a.symbol_type().elem_type.width
                tname = TS.get_timed_name(name, t)
                m = modeldic[tname]
                for i, v in m.items():
                    vcdname = name + "[%i]"%i
                    ret.append("b%s v%s"%(dec_to_bin(v,width),var2id[vcdname]))

        # make the last time step visible
        # also important for correctness, gtkwave sometimes doesn't read the
        # last timestep's values correctly without this change
        ret.append("#%d"%(t+1))

        return NL.join(ret)
