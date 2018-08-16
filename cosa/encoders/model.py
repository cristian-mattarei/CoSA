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

class ModelParser(object):
    extensions = None
    
    def __init__(self):
        pass

    def parse_string(self, string):
        Logger.error("Not implemented")

    def parse_file(self, strfile, flags=None):
        Logger.error("Not implemented")

    @staticmethod        
    def get_extensions():
        Logger.error("Not implemented")
