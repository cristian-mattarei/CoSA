# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import get_type, TRUE, FALSE, BV, BVNot

from cosa.utils.logger import Logger
from cosa.modifiers.template import ModelModifier

class NonDeterministic(ModelModifier):
    name = "NonDeterministic"
    description = "any possible value"

    def __init__(self):
        pass

    def get_behavior(self, input_var, output_var):
        return output_var

class Zero(ModelModifier):
    name = "Zero"
    description = "fixed value 0"

    def __init__(self):
        pass

    def get_behavior(self, input_var, output_var):
        vartype = get_type(output_var)
        if vartype.is_bool_type():
            return FALSE()

        assert vartype.is_bv_type()
        
        return BV(0, vartype.width)

class High(ModelModifier):
    name = "High"
    description = "fixed to the maximum value"

    def __init__(self):
        pass

    def get_behavior(self, input_var, output_var):
        vartype = get_type(output_var)
        if vartype.is_bool_type():
            return TRUE()

        assert vartype.is_bv_type()

        width = vartype.width
        return BV((2**width)-1, width)

class Inverted(ModelModifier):
    name = "Inverted"
    description = "negation of the correct value"

    def __init__(self):
        pass

    def get_behavior(self, input_var, output_var):
        vartype = get_type(input_var)
        if vartype.is_bool_type():
            return Not(input_var)

        assert vartype.is_bv_type()

        return BVNot(input_var)

    
