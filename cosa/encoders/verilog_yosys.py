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

from cosa.utils.generic import suppress_output, restore_output, check_command

PASSES = []
PASSES.append("hierarchy -check")
OPT_PASSES = []
OPT_PASSES.append("proc")
OPT_PASSES.append("opt")
OPT_PASSES.append("opt_expr -mux_undef")
OPT_PASSES.append("opt")
OPT_PASSES.append("opt")
OPT_PASSES.append("memory_dff -wr_only")
OPT_PASSES.append("memory_collect;")
OPT_PASSES.append("flatten;")
OPT_PASSES.append("memory_unpack")
OPT_PASSES.append("splitnets -driver")
OPT_PASSES.append("opt;;")
OPT_PASSES.append("memory_collect;")
OPT_PASSES.append("pmuxtree")
OPT_PASSES.append("proc")
OPT_PASSES.append("opt;;")
COMMANDS = []
COMMANDS.append("read_verilog -nomem2reg -sv {FILES}")
COMMANDS.append("prep -top {TARGET}")
COMMANDS.append("{PASSES}")
COMMANDS.append("setundef -undriven -anyseq")
COMMANDS.append("write_btor {BTORFILE}")

DFFSR2DFF_CMD = "yosys -p 'techmap -map +/dffsr2dff.v'"
TMPFILE = "__yosys_verilog__.btor2"
CMD = "yosys"
INCLUDE = "`include"
YOSYSERRLOG = "yosys-err.log"
MULTI_FILE_EXT="vlist"

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

class VerilogYosysBtorParser(ModelParser):
    parser = None
    extensions = ["v", "sv", MULTI_FILE_EXT]
    name = "Verilog Yosys (via BTOR)"

    files_from_dir = False
    single_file = True

    commands = []

    def __init__(self):
        pass

    def is_available(self):
        return shutil.which(CMD) is not None

    def get_model_info(self):
        return None

    def _get_extension(self, strfile):
        return strfile.split(".")[-1]

    def parse_file(self, filepath, config, flags=None):

        # create copy of yosys commands (will be modified below)
        # Note: This class is only instantiated once per python environment
        #       but we don't want subsequent calls to parse_file to be coupled
        COPY_PASSES = PASSES.copy()
        COPY_OPT_PASSES = OPT_PASSES.copy()
        COPY_COMMANDS = COMMANDS.copy()

        if flags is None:
            Logger.error("Top module not provided")

        if config.verific:
            COPY_COMMANDS[0] = "verific -sv2009 {FILES}; verific -import {TARGET};"

        topmodule = flags[0]
        abspath = filepath.absolute()
        directory = filepath.parent
        filename = filepath.name
        if abspath.is_dir():
            # TODO: Test this feature
            self.files_from_dir = True
        else:
            self.single_file = filename.split(".")[-1] != MULTI_FILE_EXT

        if config.no_arrays:
            COPY_PASSES.append("memory")
        else:
            COPY_PASSES.append("memory -nomap")

        if config.synchronize:
            COPY_PASSES.append("async2sync")

        if config.opt_circuit:
            for op in COPY_OPT_PASSES:
                COPY_PASSES.append(op)
        else:
            COPY_PASSES.append("flatten;")

        if not config.abstract_clock:
            COPY_PASSES.append("clk2fflogic;")
            if config.opt_circuit:
                COPY_PASSES.append("opt;;")

        if self.single_file:
            files = [str(abspath)]
        else:
            if self.files_from_dir:
                files = [str(f) for f in directory.iterdir() if f.suffix[1:] in self.extensions]
            else:
                files = []
                with abspath.open("r") as source_list:
                    Logger.msg("Reading source files from \"%s\"... "%(filename), 0)
                    for source in source_list.read().split("\n"):
                        source = source.strip()
                        if source:
                            files.append(source)

        command = "%s -p \"%s\""%(CMD, "; ".join(COPY_COMMANDS))
        command = command.format(FILES=" ".join(files), \
                                 TARGET=topmodule, \
                                 PASSES="; ".join(COPY_PASSES), \
                                 BTORFILE=TMPFILE)

        Logger.log("Command: %s"%command, 2)

        print_level = 3
        if not Logger.level(print_level):
            saved_status = suppress_output(redirect_error=True)

        retval = os.system(command)

        if not Logger.level(print_level):
            restore_output(saved_status)

        if retval != 0:
            os.system("mv %s %s"%(saved_status[0].name, YOSYSERRLOG))
            Logger.error("Error in Verilog conversion.\nSee %s for more info."%YOSYSERRLOG)

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
