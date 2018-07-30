# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, TRUE, And, BVNot, BVAnd, BVOr, BVAdd, Or, Symbol, BV, EqualsOrIff, \
    Implies, BVMul, BVExtract, BVUGT, BVULT, BVULE, Ite, BVZExt, BVXor, BVConcat, get_type, BVSub, Xor
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.representation import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import quote_names, B2BV, BV2B
from cosa.utils.generic import bin_to_dec

NL = "\n"

SN="N%s"

COM=";"
SORT="sort"
BITVEC="bitvec"
ARRAY="array"
ZERO="zero"
ONE="one"
ONES="ones"
STATE="state"
INPUT="input"
ADD="add"
EQ="eq"
NE="ne"
MUL="mul"
SLICE="slice"
CONST="const"
CONSTD="constd"
UGT="ugt"
ULT="ult"
ULTE="ulte"
AND="and"
XOR="xor"
NAND="nand"
IMPLIES="implies"
OR="or"
ITE="ite"
NOT="not"
REDOR="redor"
REDAND="redand"
UEXT="uext"
CONCAT="concat"
SUB="sub"

INIT="init"
NEXT="next"
CONSTRAINT="constraint"
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

        hts = HTS()
        ts = TS()

        nodemap = {}

        translist = []
        initlist = []
        invarlist = []

        invar_props = []
        ltl_props = []

        def getnode(nid):
            if int(nid) < 0:
                return Ite(BV2B(nodemap[str(-int(nid))]), BV(0,1), BV(1,1))
            return nodemap[nid]

        def binary_op(bvop, bop, left, right):
            if (get_type(left) == BOOL) and (get_type(right) == BOOL):
                return bop(left, right)
            return bvop(B2BV(left), B2BV(right))

        def unary_op(bvop, bop, left):
            if (get_type(left) == BOOL):
                return bop(left)
            return bvop(left)
        
        for line in strinput.split(NL):
            linetok = line.split()
            if len(linetok) == 0:
                continue
            if linetok[0] == COM:
                continue
            
            (nid, ntype, *nids) = linetok

            if ntype == SORT:
                (stype, *attr) = nids
                if stype == BITVEC:
                    nodemap[nid] = BVType(int(attr[0]))
                if stype == ARRAY:
                    assert False
                    
            if ntype == ZERO:
                nodemap[nid] = BV(0, getnode(nids[0]).width)

            if ntype == ONE:
                nodemap[nid] = BV(1, getnode(nids[0]).width)
                
            if ntype == ONES:
                width = getnode(nids[0]).width
                nodemap[nid] = BV((2**width)-1, width)

            if ntype == REDOR:
                width = get_type(getnode(nids[1])).width
                zeros = BV(0, width)
                nodemap[nid] = Not(EqualsOrIff(getnode(nids[1]), zeros))

            if ntype == REDAND:
                width = get_type(getnode(nids[1])).width
                ones = BV((2**width)-1, width)
                nodemap[nid] = EqualsOrIff(getnode(nids[1]), ones)
                
            if ntype == CONSTD:
                width = getnode(nids[0]).width
                nodemap[nid] = BV(int(nids[1]), width)

            if ntype == CONST:
                width = getnode(nids[0]).width
                nodemap[nid] = BV(bin_to_dec(nids[1]), width)
                
            if ntype in [STATE, INPUT]:
                if len(nids) > 1:
                    nodemap[nid] = Symbol(nids[1], getnode(nids[0]))
                else:
                    nodemap[nid] = Symbol((SN%nid), getnode(nids[0]))
                if ntype == INPUT:
                    ts.add_input_var(nodemap[nid])
                else:
                    ts.add_state_var(nodemap[nid])

            if ntype == AND:
                nodemap[nid] = binary_op(BVAnd, And, getnode(nids[1]), getnode(nids[2]))

            if ntype == CONCAT:
                nodemap[nid] = BVConcat(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))
                
            if ntype == XOR:
                nodemap[nid] = binary_op(BVXor, Xor, getnode(nids[1]), getnode(nids[2]))
                
            if ntype == NAND:
                bvop = lambda x,y: BVNot(BVAnd(x, y))
                bop = lambda x,y: Not(And(x, y))
                nodemap[nid] = binary_op(bvop, bop, getnode(nids[1]), getnode(nids[2]))

            if ntype == IMPLIES:
                nodemap[nid] = Implies(BV2B(getnode(nids[1])), BV2B(getnode(nids[2])))
                
            if ntype == NOT:
                nodemap[nid] = unary_op(BVNot, Not, getnode(nids[1]))
                
            if ntype == UEXT:
                nodemap[nid] = BVZExt(B2BV(getnode(nids[1])), int(nids[2]))
                
            if ntype == OR:
                nodemap[nid] = binary_op(BVOr, Or, getnode(nids[1]), getnode(nids[2]))
                
            if ntype == ADD:
                nodemap[nid] = BVAdd(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == SUB:
                nodemap[nid] = BVSub(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))
                
            if ntype == UGT:
                nodemap[nid] = BVUGT(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == ULT:
                nodemap[nid] = BVULT(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == ULTE:
                nodemap[nid] = BVULE(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))
                
            if ntype == EQ:
                nodemap[nid] = EqualsOrIff(getnode(nids[1]), getnode(nids[2]))

            if ntype == NE:
                nodemap[nid] = Not(EqualsOrIff(getnode(nids[1]), getnode(nids[2])))
                
            if ntype == MUL:
                nodemap[nid] = BVMul(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == SLICE:
                nodemap[nid] = BVExtract(B2BV(getnode(nids[1])), int(nids[3]), int(nids[2]))

            if ntype == ITE:
                if (get_type(getnode(nids[2])) == BOOL) or (get_type(getnode(nids[3])) == BOOL):
                    nodemap[nid] = Ite(BV2B(getnode(nids[1])), BV2B(getnode(nids[2])), BV2B(getnode(nids[3])))
                else:
                    nodemap[nid] = Ite(BV2B(getnode(nids[1])), getnode(nids[2]), getnode(nids[3]))
                
            if ntype == NEXT:
                if (get_type(getnode(nids[1])) == BOOL) or (get_type(getnode(nids[2])) == BOOL):
                    nodemap[nid] = EqualsOrIff(BV2B(TS.get_prime(getnode(nids[1]))), BV2B(getnode(nids[2])))
                else:
                    nodemap[nid] = EqualsOrIff(TS.get_prime(getnode(nids[1])), getnode(nids[2]))
                translist.append(nodemap[nid])

            if ntype == INIT:
                if (get_type(getnode(nids[1])) == BOOL) or (get_type(getnode(nids[2])) == BOOL):
                    nodemap[nid] = EqualsOrIff(BV2B(getnode(nids[1])), BV2B(getnode(nids[2])))
                else:
                    nodemap[nid] = EqualsOrIff(getnode(nids[1]), getnode(nids[2]))
                initlist.append(nodemap[nid])

            if ntype == CONSTRAINT:
                nodemap[nid] = BV2B(getnode(nids[0]))
                invarlist.append(nodemap[nid])
                
            if ntype == BAD:
                nodemap[nid] = getnode(nids[0])
                invar_props.append(Not(BV2B(nodemap[nid])))

            if nid not in nodemap:
                Logger.error("Unknown node type \"%s\""%ntype)
                
        init = And(initlist)
        trans = And(translist)
        invar = And(invarlist)

        ts.set_behavior(init, trans, invar)
        hts.add_ts(ts)

        return (hts, invar_props, ltl_props)
