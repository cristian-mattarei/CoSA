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
        

class SymbolsWalker(IdentityDagWalker):
    symbols = set([])

    def reset_symbols(self):
        self.symbols = set([])
    
    def walk_symbol(self, formula, args, **kwargs):
        self.symbols.add(formula)
        return formula
        
    
subwalker = SubstituteWalker(invalidate_memoization=True)
symwalker = SymbolsWalker(invalidate_memoization=True)

def substitute(formula, mapsym):
    subwalker.set_substitute_map(mapsym)
    return subwalker.walk(formula)

def get_free_variables(formula):
    symwalker.reset_symbols()
    symwalker.walk(formula)
    return symwalker.symbols
