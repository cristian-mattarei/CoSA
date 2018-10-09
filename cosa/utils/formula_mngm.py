# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import re

from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.shortcuts import Ite, EqualsOrIff, BV, get_type
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.utils.generic import new_string

def B2BV(f):
    if get_type(f).is_bv_type():
        return f
    return Ite(f, BV(1,1), BV(0,1))
    
def BV2B(f):
    if get_type(f).is_bool_type():
        return f
    return EqualsOrIff(f, BV(1,1))

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
    
def substitute(formula, mapsym, reset_walker=False):
    subwalker = SubstituteWalker()
    subwalker.set_substitute_map(mapsym)
    return subwalker.walk(formula)

def get_free_variables(formula):
    symwalker = SymbolsWalker()
    symwalker.reset_symbols()
    symwalker.walk(formula)
    return symwalker.symbols

KEYWORDS = ["not","xor","False","True","next","prev","G","F","X","U","R","O","H","xor","ZEXT","bvcomp"]
OPERATORS = [(" < "," u< "), \
             (" > "," u> "), \
             (" >= "," u>= "), \
             (" <= "," u<= ")]

def quote_names(strformula, prefix=None, replace_ops=True):
    lst_names = []
    if (prefix is not None) and (prefix != ""):
        lst_names.append(prefix)
    strformula = strformula.replace("\\","")

    lits = [(len(x), x) for x in list(re.findall("([a-zA-Z][a-zA-Z_$\.0-9]*)+", strformula)) if x not in KEYWORDS]
    lits.sort()
    lits.reverse()
    lits = [x[1] for x in lits]
    
    repl_lst = []
    
    for lit in lits:
        newlit = new_string()
        strformula = strformula.replace("\'%s\'"%lit, lit)
        strformula = strformula.replace(lit, newlit)
        repl_lst.append((newlit, lit))

    for (newlit, lit) in repl_lst:
        strformula = strformula.replace(newlit, "\'%s\'"%(".".join(lst_names+[lit])))
    if replace_ops:
        for op in OPERATORS:
            strformula = strformula.replace(op[0], op[1])

    return strformula

def mem_access(address, locations, width_idx, idx=0):
    if (len(locations) == 1) or (idx == 2**width_idx):
        return locations[0]
    location = BV(idx, width_idx)
    return Ite(EqualsOrIff(address, location), locations[0], mem_access(address, locations[1:], width_idx, idx+1))
