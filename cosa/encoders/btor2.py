# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import TRUE, And, BVAdd, Or, Symbol, BV, EqualsOrIff, Implies
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.representation import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import quote_names

NL = "\n"

SN="N%s"

SORT="sort"
BITVEC="bitvec"
ARRAY="array"
ZERO="zero"
ONE="one"
ONES="ones"
STATE="state"
ADD="add"
EQ="eq"
INIT="init"
NEXT="next"
EQ="eq"
BAD="bad"

class BTOR2Parser(object):
    parser = None
    extension = "btor2"
    
    def __init__(self):
        pass

    def parse_file(self, strfile, flags=None):
        with open(strfile, "r") as f:
            return self.parse_string(f.read())

    def get_extension(self):
        return self.extension

    @staticmethod        
    def get_extension():
        return BTOR2Parser.extension

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name
    
    def parse_string(self, strinput):

        hts = HTS("")
        
        nodemap = {}

        translist = []
        initlist = []
        vars = set([])
        
        for line in strinput.split(NL):
            linetok = line.split()

            (nid, ntype, *nids) = linetok

            if ntype == SORT:
                (stype, *attr) = nids
                if stype == BITVEC:
                    nodemap[nid] = BVType(int(attr[0]))
                if stype == ARRAY:
                    assert False
                    
            if ntype == ZERO:
                nodemap[nid] = BV(0, nodemap[nids[0]].width)

            if ntype == ONE:
                nodemap[nid] = BV(1, nodemap[nids[0]].width)
                
            if ntype == ONES:
                width = nodemap[nids[0]].width
                nodemap[nid] = BV((2**width)-1, width)

            if ntype == STATE:
                nodemap[nid] = Symbol((SN%nid), nodemap[nids[0]])
                vars.add(nodemap[nid])

            if ntype == ADD:
                nodemap[nid] = BVAdd(nodemap[nids[1]], nodemap[nids[2]])

            if ntype == EQ:
                nodemap[nid] = EqualsOrIff(nodemap[nids[1]], nodemap[nids[2]])

            if ntype == NEXT:
                nodemap[nid] = EqualsOrIff(TS.get_prime(nodemap[nids[1]]), nodemap[nids[2]])
                translist.append(nid)

            if ntype == INIT:
                nodemap[nid] = EqualsOrIff(nodemap[nids[1]], nodemap[nids[2]])
                initlist.append(nid)
                
        init = And([nodemap[x] for x in initlist])
        trans = And([nodemap[x] for x in translist])
        invar = TRUE()

        hts.add_ts(TS(vars, init, trans, invar))
            
        return hts
