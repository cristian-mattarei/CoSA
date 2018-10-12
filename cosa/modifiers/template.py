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


class ModelModifier(object):
    name = "GENERATOR"
    description = "MISSING DESCRIPTION!"

    def __init__(self):
        pass

    def get_behavior(self, input_var, output_var):
        Logger.error("Behavior definition is not implemented")
        
    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

