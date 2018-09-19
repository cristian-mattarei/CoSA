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
from cosa.encoders.btor2 import BTOR2Parser

from cosa.utils.generic import suppress_output, restore_output

PASSES = []
PASSES.append("hierarchy -check")
PASSES.append("proc")
PASSES.append("flatten")
PASSES.append("memory")
PASSES.append("techmap -map +/adff2dff.v")
PASSES.append("setundef -zero -undriven")
PASSES.append("pmuxtree")
PASSES.append("rename -hide")
PASSES.append("proc")
PASSES.append("clk2fflogic")
PASSES.append("opt")

COMMANDS = []
COMMANDS.append("read_verilog -sv {FILES}")
COMMANDS.append("hierarchy -top {TARGET}")
COMMANDS.append("{PASSES}")
COMMANDS.append("write_btor -v {BTORFILE}")

TMPFILE = "__yosys_verilog__.btor2"

CMD = "yosys"

INCLUDE = "`include"

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

class VerilogYosysBtorParser(ModelParser):
    parser = None
    extensions = ["v"]
    name = "Verilog Yosys (via BTOR)"

    files_from_dir = False
    single_file = True
    
    def __init__(self):
        pass

    def is_available(self):
        return shutil.which(CMD) is not None

    def get_model_info(self):
        return None
     
    def _get_extension(self, strfile):
        return strfile.split(".")[-1]

    def _collect_dependencies(self, path, top, skip=[]):
        new_filenames = []
        
        with open("%s/%s"%(path, top), "r") as f:
            filestr = f.read()
            filestr = re.sub('(//)(.*)',' ', filestr)
            for line in filestr.split("\n"):
                line = re.sub('\t+',' ', re.sub(' +',' ', line))
                if line.strip() == "":
                    continue
                if INCLUDE in line:
                    new_filenames.append(re.search("\".+\"", line).group(0)[1:-1])
                    continue
                instantiations = re.search("([a-zA-Z][a-zA-Z_0-9]*)+( )", line)

                if instantiations is not None:
                    instance = instantiations.group(0)[:-1]
                    if (instance in skip) or (instance in KEYWORDS):
                        continue
                    filename = "%s.v"%instance
                    if os.path.isfile("%s/%s"%(path, filename)):
                        new_filenames.append("%s.v"%instance)
                    skip.append(instance)
 
        skip.append(top)
                            
        for filename in new_filenames:
            new_filenames += self._collect_dependencies(path, filename, skip)

        return new_filenames
    
    def parse_file(self, strfile, config, flags=None):
        if flags is None:
            Logger.error("Top module not provided")

        topmodule = flags[0]
        absstrfile = os.path.abspath(strfile)
        directory = "/".join(absstrfile.split("/")[:-1])
        filename = absstrfile.split("/")[-1]

        if self.single_file:
            files = [absstrfile]
        else:
            if self.files_from_dir:
                files = ["%s/%s"%(directory, f) for f in os.listdir(directory) if self._get_extension(f) in self.extensions]
            else:
                files = ["%s/%s"%(directory, f) for f in list(set(self._collect_dependencies(directory, filename)))]
                files.append(absstrfile)

        command = "%s -p \"%s\""%(CMD, "; ".join(COMMANDS))
        command = command.format(FILES=" ".join(files), \
                                 TARGET=topmodule, \
                                 PASSES="; ".join(PASSES), \
                                 BTORFILE=TMPFILE)

        Logger.log("Command: %s"%command, 2)

        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()
        
        retval = os.system(command)

        if not Logger.level(print_level):
            restore_output(saved_stdout)

        if retval != 0:
            Logger.error("Error in Verilog conversion")
            
        parser = BTOR2Parser()
        ret = parser.parse_file(TMPFILE, config)

        if not Logger.level(1):
            os.remove(TMPFILE)
        
        return ret

    def get_extensions(self):
        return self.extensions

    @staticmethod        
    def get_extensions():
        return VerilogYosysBtorParser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name
    
    def parse_string(self, strinput):
        return

        return (hts, invar_props, ltl_props)
