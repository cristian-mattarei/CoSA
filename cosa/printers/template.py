# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from six.moves import cStringIO

from cosa.utils.logger import Logger

class HTSPrinterType(object):
    NONE = 0

    c_size = 10
    ####################

    SMV = 11
    STS = 12

    TRANSSYS = 20

    ####################

class TraceValuesBase(object):
    BV = "BV"
    HEX = "HEX"
    BIN = "BIN"

    @staticmethod
    def get_all():
        return [TraceValuesBase.BV, TraceValuesBase.HEX, TraceValuesBase.BIN]
    
class HTSPrinter(object):
    name = "PRINTER"
    description = "MISSING DESCRIPTION!"
    TYPE = HTSPrinterType.NONE
    EXT  = ".none"

    def __init__(self):
        self.stream = cStringIO()

    def print_hts(self, hts):
        Logger.error("Not implemented")

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

# Variables starting with HIDDEN are not printed
HIDDEN_VAR = "H__"
    
class TracePrinter(object):

    def __init__(self):
        pass

    def print_trace(self, hts, model, length, map_function=None):
        Logger.error("Not implemented")

    def get_file_ext(self):
        Logger.error("Not implemented")

    def is_hidden(self, name):
        return HIDDEN_VAR in name
