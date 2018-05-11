# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.walkers.identitydag import IdentityDagWalker
import math

def is_number(strnum):
    try:
        int(strnum)
        return True
    except:
        return False

def auto_convert(strval):
    if (strval.upper() == "TRUE") or (strval.upper() == "YES"):
        return True
    if (strval.upper() == "FALSE") or (strval.upper() == "NO"):
        return False
    try:
        return int(strval)
    except Exception:
        try:
            return float(strval)
        except Exception:
            return strval
    
def status_bar(status, length=30):
    curr = math.ceil(length*status)
    return "["+("="*(curr-1))+">"+(" "*(length-curr))+"]"+(" %.2f%%"%(status*100))
        
class SubstituteWalker(IdentityDagWalker):

    def set_substitute_function(self, function):
        self.substitute_function = function

    def set_substitute_map(self, smap):
        self.mapsymbols = smap

    def walk_symbol(self, formula, args, **kwargs):
        if formula.symbol_name() in self.mapsymbols:
            return self.mgr.Symbol(self.mapsymbols[formula.symbol_name()],
                                   formula.symbol_type())
        else:
            return self.mgr.Symbol(formula.symbol_name(),
                                   formula.symbol_type())
        
