# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os
import shutil
import re

from cosa.representation import HTS, TS
from cosa.utils.logger import Logger

from cosa.encoders.template import ModelParser
from cosa.encoders.verilog_hts import VerilogHTSParser

from cosa.utils.generic import suppress_output, restore_output

COMMANDS = []
COMMANDS.append("read -sysv {FILES} -top {TARGET}")
COMMANDS.append("write -format verilog {FILE}")

TMPFILE = "__verific_verilog__.v"
TMPCMDFILE = "__verific_commands__.txt"

CMD = "verific"

class SystemVerilogVerificParser(ModelParser):
    parser = None
    extensions = ["sv"]
    name = "SystemVerilog (Verific)"

    model_info = None

    def __init__(self):
        pass

    def is_available(self):
        if shutil.which(CMD) is None:
            return False

        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()
        
        retval = os.system("%s -h"%CMD)

        if not Logger.level(print_level):
            restore_output(saved_stdout)

        if retval != 0:
            return False
        
        return True

    def get_model_info(self):
        return self.model_info
     
    def parse_file(self, strfile, config, flags=None):
        if flags is None:
            Logger.error("Top module not provided")

        topmodule = flags[0]
        absstrfile = os.path.abspath(strfile)
        directory = "/".join(absstrfile.split("/")[:-1])
        filename = absstrfile.split("/")[-1]

        files = [absstrfile]

        with open(strfile, "r") as f:
            if topmodule not in f.read():
                Logger.error("Module \"%s\" not found"%topmodule)
            
        commands = "\n".join(COMMANDS)
        commands = commands.format(FILES=" ".join(files), \
                                   TARGET=topmodule, \
                                   FILE=TMPFILE)

        command = "%s -script_file %s"%(CMD, TMPCMDFILE)
        
        with open(TMPCMDFILE, "w") as f:
            f.write(commands)
        
        Logger.log("Commands: %s"%commands, 2)

        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()
        
        retval = os.system(command)

        if not Logger.level(print_level):
            restore_output(saved_stdout)

        if retval != 0:
            Logger.error("Error in SystemVerilog conversion")
            
        parser = VerilogHTSParser()
        ret = parser.parse_file(TMPFILE, config, flags=flags)
        self.model_info = parser.get_model_info()

        if (not Logger.level(1)) and (not config.devel):
            os.remove(TMPFILE)
            os.remove(TMPCMDFILE)
        
        return ret

    def get_extensions(self):
        return self.extensions

    @staticmethod        
    def get_extensions():
        return SystemVerilogVerificParser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name
    
    def parse_string(self, strinput):
        return

        return (hts, invar_props, ltl_props)
