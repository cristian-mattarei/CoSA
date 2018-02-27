# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.printers import HRPrinter
from pysmt.walkers import TreeWalker
from pysmt.utils import quote
from core.transition_system import TS

from pysmt.shortcuts import Symbol

from six.moves import cStringIO

class NotRegisteredPrinterException(Exception):
    pass

class PrinterType(object):
    NONE = 0
    
    c_size = 10
    ####################

    SMV = 11
    
    TRANSSYS = 20
    
    ####################

class PrintersFactory(object):
    printers = []
    default_printer = None

    # Additional printers should be registered here #
    @staticmethod
    def init_printers():
        PrintersFactory.register_printer(SMVHTSPrinter(), True)

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
            raise NotRegisteredPrinterException
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

    def print_hts(self, hts):

        self.write("MODULE main\n\n")

        for var in hts.vars:
            self.write("VAR %s : word[%s];\n"%(var.symbol_name(), var.symbol_type().width))

        self.write("\nINIT\n")
        self.printer(hts.single_init())

        self.write("\n\nDEFINE\n")
        for var in hts.vars:
            self.write("%s := next(%s);\n"%(TS.get_prime(var).symbol_name(), var.symbol_name()))
        
        self.write("\nTRANS\n")
        self.printer(hts.single_trans())

        self.write("\n\nINVAR\n")
        self.printer(hts.single_invar())

        return self.stream.getvalue()
        
    
class SMVPrinter(HRPrinter):

    # Override walkers for SMV specific syntax
        
    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("TRUE")
        else:
            self.write("FALSE")

    def walk_bv_constant(self, formula):
        self.write("0ud%d_%d" % (formula.bv_width(), formula.constant_value()))
