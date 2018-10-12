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

class ModelModifiersFactory(object):
    modifiers = []

    # Additional modifiers should be registered here #
    @staticmethod
    def init_modifiers():
        from cosa.modifiers.behavior import NonDeterministic, Zero, High, Inverted
    
        ModelModifiersFactory.register_modifier(NonDeterministic(), True)
        ModelModifiersFactory.register_modifier(Zero())
        ModelModifiersFactory.register_modifier(High())
        ModelModifiersFactory.register_modifier(Inverted())
        
    @staticmethod
    def register_modifier(modifier, default=False):
        if modifier.get_name() not in dict(ModelModifiersFactory.modifiers):
            ModelModifiersFactory.modifiers.append((modifier.get_name(), modifier))

        if default:
            ModelModifiersFactory.default = modifier
            
    @staticmethod
    def modifier_names():
        return [x[0] for x in ModelModifiersFactory.modifiers]

    @staticmethod
    def get_default():
        return ModelModifiersFactory.default
    
    @staticmethod
    def get_modifiers():
        ModelModifiersFactory.init_modifiers()
        return [x[1] for x in ModelModifiersFactory.modifiers]

    @staticmethod
    def modifier_by_name(name):
        ModelModifiersFactory.init_modifiers()
        dmodifier = dict(ModelModifiersFactory.modifiers)
        if name not in dmodifier:
            Logger.error("Modifier \"%s\" is not registered"%name)
        return dmodifier[name]
    
