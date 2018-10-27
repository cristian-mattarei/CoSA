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
from pysmt.shortcuts import Ite, EqualsOrIff, BV, get_type, simplify, And, Or
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

free_variables_dic = {}

def get_free_variables(formula):
    if formula in free_variables_dic:
        return free_variables_dic[formula]
    symwalker = SymbolsWalker()
    symwalker.reset_symbols()
    symwalker.walk(formula)
    ret = symwalker.symbols
    free_variables_dic[formula] = ret
    return ret

KEYWORDS = ["not","xor",\
            "False","True",\
            "next","prev",\
            "G","F","X","U","R","O","H",\
            "ZEXT","bvcomp",\
            "a>>"]
OPERATORS = [(" < "," u< "), \
             (" > "," u> "), \
             (" >= "," u>= "), \
             (" <= "," u<= ")]

def quote_names(strformula, prefix=None, replace_ops=True):
    lst_names = []
    if (prefix is not None) and (prefix != ""):
        lst_names.append(prefix)
    strformula = strformula.replace("\\","")

    for i in range(len(KEYWORDS)):
        strformula = strformula.replace(" %s "%(KEYWORDS[i]), "@@%d@@"%i)
    
    lits = [(len(x), x) for x in list(re.findall("([a-zA-Z][a-zA-|Z_$\.0-9\[\]]*)+", strformula)) if x not in KEYWORDS]
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

    for i in range(len(KEYWORDS)):
        strformula = strformula.replace("@@%d@@"%i, " %s "%(KEYWORDS[i]))
        
    if replace_ops:
        for op in OPERATORS:
            strformula = strformula.replace(op[0], op[1])

    return strformula

def mem_access(address, locations, width_idx, idx=0):
    if (len(locations) == 1) or (idx == 2**width_idx):
        return locations[0]
    location = BV(idx, width_idx)
    return Ite(EqualsOrIff(address, location), locations[0], mem_access(address, locations[1:], width_idx, idx+1))


class SortingNetwork(object):
    simplify = False
    
    @staticmethod
    def sorting_network(inputs):
        if len(inputs) == 0:
            return []
        return SortingNetwork.sorting_network_int(inputs)
    
    @staticmethod
    def sorting_network_int(inputs):
        if len(inputs) == 1:
            return inputs;

        if len(inputs) == 2:
            el1 = inputs[0]
            el2 = inputs[1]
            return SortingNetwork.two_comparator(el1, el2)

        pivot = int(len(inputs) / 2)
        left_inputs = inputs[:pivot]
        right_inputs = inputs[pivot:]

        left_outputs = SortingNetwork.sorting_network_int(left_inputs)
        right_outputs = SortingNetwork.sorting_network_int(right_inputs)
        
        outputs = SortingNetwork.merge(left_outputs, right_outputs)

        return outputs

    # Basic comparator for two inputs.
    @staticmethod
    def two_comparator(input1, input2):
        if SortingNetwork.simplify:
            return [simplify(Or(input1, input2)), simplify(And(input1, input2))]
        else:
            return [Or(input1, input2), And(input1, input2)]

    # Function that merges two arrays of signals.
    @staticmethod
    def merge(input1, input2):
        output = []

        if len(input1) == 0:
            return input2

        if len(input2) == 0:
            return input1

        if (len(input1) == 1) and (len(input2) == 1):
            el1 = input1[0]
            el2 = input2[0];
            return SortingNetwork.two_comparator(el1, el2);


        is_input1_even = ((len(input1) % 2) == 0)
        is_input2_even = ((len(input2) % 2) == 0)

        is_input1_odd = not is_input1_even
        is_input2_odd = not is_input2_even

        if is_input1_odd and is_input2_even:
            return SortingNetwork.merge(input2, input1)

        size_h1 = (len(input1) / 2);
        res_h1 = (len(input1) % 2);
        input1_odd = []
        input1_even = []

        for i in range(len(input1)):
            element = input1[i]
            if (((i+1)%2) == 0):
                input1_even.append(element)
            else:
                input1_odd.append(element)

        size_h2 = (len(input2) / 2);
        res_h2 = (len(input2) % 2);
        input2_odd = []
        input2_even = []

        for i in range(len(input2)):
            element = input2[i]
            if (((i+1)%2) == 0):
                input2_even.append(element)
            else:
                input2_odd.append(element)

        output_odd = SortingNetwork.merge(input1_odd, input2_odd);
        output_even = SortingNetwork.merge(input1_even, input2_even);

        # is_input1_even && is_input2_even

        if is_input1_even and is_input2_even:
            first_output_odd = output_odd[0]
            last_output_even = output_even[-1]
            
            output.append(first_output_odd)
            
            for i in range(len(output_odd) - 1):
                el_odd = output_odd[i+1]
                el_even = output_even[i]

                res = SortingNetwork.two_comparator(el_odd, el_even)
                output.append(res[0])
                output.append(res[1])

            output.append(last_output_even)

        # end of is_input1_even && is_input2_even

        
        if is_input1_even and is_input2_odd:

            first_output_odd = output_odd[0]

            output.append(first_output_odd)

            for i in range(len(output_even)):
                el_odd = output_odd[i+1]
                el_even = output_even[i]

                res = SortingNetwork.two_comparator(el_odd, el_even)
                output.append(res[0])
                output.append(res[1])

        # end of is_input1_even && is_input2_odd


        if is_input1_odd and is_input2_odd:

            first_output_odd = output_odd[0]
            last_output_odd = output_odd[-1]

            output.append(first_output_odd)

            for i in range(len(output_even)):
                el_odd = output_odd[i+1]
                el_even = output_even[i]

                res = SortingNetwork.two_comparator(el_odd, el_even)
                output.append(res[0])
                output.append(res[1])

            output.append(last_output_odd)

        # end of is_input1_odd && is_input2_odd

        assert((len(input1)+len(input2)) == len(output))

        return output

