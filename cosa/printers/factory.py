# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.printers.hts import SMVHTSPrinter, STSHTSPrinter
from cosa.printers.template import HTSPrinterType

class HTSPrintersFactory(object):
    printers = []
    default_printer = None

    # Additional printers should be registered here #
    @staticmethod
    def init_printers():
        HTSPrintersFactory.register_printer(STSHTSPrinter(), True)
        HTSPrintersFactory.register_printer(SMVHTSPrinter(), False)

    @staticmethod
    def get_default():
        return HTSPrintersFactory.default_printer

    @staticmethod
    def register_printer(printer, default=False):
        if printer.get_name() not in dict(HTSPrintersFactory.printers):
            HTSPrintersFactory.printers.append((printer.get_name(), printer))
            if default:
                HTSPrintersFactory.default_printer = printer

    @staticmethod
    def printer_by_name(name):
        HTSPrintersFactory.init_printers()
        dprint = dict(HTSPrintersFactory.printers)
        if name not in dprint:
            Logger.error("Printer \"%s\" is not registered"%name)
        return dprint[name]

    @staticmethod
    def get_printers():
        HTSPrintersFactory.init_printers()
        return [x[0] for x in HTSPrintersFactory.printers]

    @staticmethod
    def get_printers_by_type(printertype):
        HTSPrintersFactory.init_printers()
        if (printertype % HTSPrinterType.c_size) == 0:
            return [x[1] for x in HTSPrintersFactory.printers \
                    if (x[1].TYPE < printertype) and (x[1].TYPE >= printertype-HTSPrinterType.c_size)]

        return [x[1] for x in HTSPrintersFactory.printers if x[1].TYPE == printertype]
