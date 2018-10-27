# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.utils.logger import Logger

class ModelFlags(object):
    NO_INIT = "NO-INIT"

class EncoderConfig(object):
    abstract_clock = False
    symbolic_init = False
    zero_init = False
    add_clock = False
    deterministic = False
    run_passes = True
    boolean = False
    debug = False

    def __init__(self):
        pass

class ModelInformation(object):

    abstract_clock_list = None
    clock_list = None
    
    def __init__(self):
        self.abstract_clock_list = []
        self.clock_list = []

    def combine(self, other):
        if other is not None:
            if other.abstract_clock_list is not None:
                for el in other.abstract_clock_list:
                    if el not in self.abstract_clock_list:
                        self.abstract_clock_list.append(el)
            if other.clock_list is not None:
                for el in other.clock_list:
                    if el not in self.clock_list:
                        self.clock_list.append(el)

    def __repr__(self):
        return "CL(%s) ACL(%s)"%(", ".join([str(s) for s in self.clock_list]) if self.clock_list is not None else "", \
                                 ", ".join([str(s) for s in self.abstract_clock_list]) if self.abstract_clock_list is not None else "")
                
class ModelParser(object):
    extensions = None
    name = None
    config = None
    
    def __init__(self):
        pass

    def parse_string(self, string):
        Logger.error("Not implemented")

    def parse_file(self, strfile, config, flags=None):
        Logger.error("Not implemented")

    def get_name(self):
        return self.name
        
    @staticmethod        
    def get_extensions():
        Logger.error("Not implemented")

    def is_available(self):
        Logger.error("Not implemented")

    def get_model_info(self):
        Logger.error("Not implemented")
        
from pysmt.parsing import Rule
        
class SyntacticSugar(object):
    name = "Syntactic Sugar"
    description = "MISSING DESCRIPTION!"
    interface = "MISSING INTERFACE!"

    encoder_config = None

    def __init__(self, encoder_config):
        self.encoder_config = encoder_config

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def get_interface(self):
        return self.interface
    
    def insert_lexer_rule(self, rules):
        rules.insert(0, Rule(r"(%s)"%self.name, self.adapter(), False))

    def adapter(self):
        Logger.error("Adapter not implemented")
        
class STSGenerator(object):
    name = "GENERATOR"
    description = "MISSING DESCRIPTION!"
    interface = "MISSING INTERFACE!"

    def __init__(self):
        pass

    def get_sts(self, name, params):
        if len(list(params)) != self.get_param_length():
            Logger.error("Not correct parameters for generator \"%s\""%(self.name))
        return self.compile_sts(name, params)

    def compile_sts(name, params):
        Logger.error("Compile STS not Implemented")
    
    def get_param_length(self):
        Logger.error("Param length not Implemented")
        
    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def get_interface(self):
        return self.interface

class ClockBehavior(object):
    name = "CLOCK BEHAVIOR"
    description = "MISSING DESCRIPTION!"
    interface = "MISSING INTERFACE!"

    def __init__(self):
        pass

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def get_interface(self):
        return self.interface
    
    def get_sts(self, params):
        Logger.error("Param length not Implemented")

    def get_default(self, params):
        Logger.error("Param length not Implemented")
        
