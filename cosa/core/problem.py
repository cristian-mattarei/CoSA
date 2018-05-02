# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


class MCProblem(object):

    properties = None
    lemmas = None
    assumptions = None
    
    def __init__(self, model):
        self.model = model
        self.properties = []
        self.lemmas = []
        self.assumptions = []

    def add_property(self, prop):
        self.properties.append(prop)

    def add_lemma(self, lemma):
        self.lemmas.append(lemma)

    def add_assumption(self, assumption):
        self.assumptions.append(assumption)
        
class SafetyMCProblem(MCProblem):
    config = None

class LivenessMCProblem(MCProblem):
    config = None
    
class EquivalenceMCProblem(MCProblem):
    config = None
    comp_model = None

class SimulationMCProblem(MCProblem):
    config = None
