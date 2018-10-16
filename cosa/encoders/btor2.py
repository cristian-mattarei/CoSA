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
    Implies, BVMul, BVExtract, BVUGT, BVUGE, BVULT, BVULE, Ite, BVZExt, BVXor, BVConcat, get_type, BVSub, \
    Xor, Select, Store, BVComp, simplify, BVLShl, BVAShr, BVLShr
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.representation import HTS, TS
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import quote_names, B2BV, BV2B
from cosa.utils.generic import bin_to_dec
from cosa.encoders.template import ModelParser

NL = "\n"

SN="N%s"

COM=";"
SORT="sort"
BITVEC="bitvec"
ARRAY="array"
WRITE="write"
READ="read"
ZERO="zero"
ONE="one"
ONES="ones"
STATE="state"
INPUT="input"
OUTPUT="output"
ADD="add"
EQ="eq"
NE="ne"
MUL="mul"
SLICE="slice"
CONST="const"
CONSTD="constd"
UGT="ugt"
UGTE="ugte"
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
SLL="sll"
SRA="sra"
SRL="srl"

INIT="init"
NEXT="next"
CONSTRAINT="constraint"
BAD="bad"

class BTOR2Parser(ModelParser):
    parser = None
    extensions = ["btor2","btor"]
    name = "BTOR2"
    symbolic_init = False

    def __init__(self):
        pass

    def get_model_info(self):
        return None

    def parse_file(self, strfile, config, flags=None):
        self.symbolic_init = config.symbolic_init
        with open(strfile, "r") as f:
            return self.parse_string(f.read())

    def is_available(self):
        return True
        
    def get_extensions(self):
        return self.extensions

    @staticmethod
    def get_extensions():
        return BTOR2Parser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

    def parse_string(self, strinput):

        hts = HTS()
        ts = TS()

        nodemap = {}
        node_covered = set([])

        translist = []
        initlist = []
        invarlist = []

        invar_props = []
        ltl_props = []

        def getnode(nid):
            node_covered.add(nid)
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
                    node_covered.add(nid)
                if stype == ARRAY:
                    nodemap[nid] = ArrayType(getnode(attr[0]), getnode(attr[1]))
                    node_covered.add(nid)

            if ntype == WRITE:
                nodemap[nid] = Store(*[getnode(n) for n in nids[1:4]])

            if ntype == READ:
                nodemap[nid] = Select(getnode(nids[1]), getnode(nids[2]))

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
                nodemap[nid] = BVNot(BVComp(getnode(nids[1]), zeros))

            if ntype == REDAND:
                width = get_type(getnode(nids[1])).width
                ones = BV((2**width)-1, width)
                nodemap[nid] = BVComp(getnode(nids[1]), ones)

            if ntype == CONSTD:
                width = getnode(nids[0]).width
                nodemap[nid] = BV(int(nids[1]), width)

            if ntype == CONST:
                width = getnode(nids[0]).width
                nodemap[nid] = BV(bin_to_dec(nids[1]), width)

            if ntype == STATE:
                if len(nids) > 1:
                    nodemap[nid] = Symbol(nids[1], getnode(nids[0]))
                else:
                    nodemap[nid] = Symbol((SN%nid), getnode(nids[0]))
                ts.add_state_var(nodemap[nid])

            if ntype == INPUT:
                if len(nids) > 1:
                    nodemap[nid] = Symbol(nids[1], getnode(nids[0]))
                else:
                    nodemap[nid] = Symbol((SN%nid), getnode(nids[0]))
                ts.add_input_var(nodemap[nid])

            if ntype == OUTPUT:
                if len(nids) > 2:
                    symbol = Symbol(nids[2], getnode(nids[0]))
                else:
                    symbol = Symbol((SN%nid), getnode(nids[0]))

                nodemap[nid] = EqualsOrIff(symbol, B2BV(getnode(nids[1])))
                invarlist.append(nodemap[nid])
                node_covered.add(nid)
                ts.add_output_var(symbol)

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
                nodemap[nid] = BVOr(BVNot(getnode(nids[1])), getnode(nids[2]))

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

            if ntype == UGTE:
                nodemap[nid] = BVUGE(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == ULT:
                nodemap[nid] = BVULT(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == ULTE:
                nodemap[nid] = BVULE(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == EQ:
                nodemap[nid] = BVComp(getnode(nids[1]), getnode(nids[2]))

            if ntype == NE:
                nodemap[nid] = BVNot(BVComp(getnode(nids[1]), getnode(nids[2])))

            if ntype == MUL:
                nodemap[nid] = BVMul(B2BV(getnode(nids[1])), B2BV(getnode(nids[2])))

            if ntype == SLICE:
                nodemap[nid] = BVExtract(B2BV(getnode(nids[1])), int(nids[3]), int(nids[2]))

            if ntype == SLL:
                nodemap[nid] = BVLShl(getnode(nids[1]), getnode(nids[2]))

            if ntype == SRA:
                nodemap[nid] = BVAShr(getnode(nids[1]), getnode(nids[2]))

            if ntype == SRL:
                nodemap[nid] = BVLShr(getnode(nids[1]), getnode(nids[2]))

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
                translist.append(getnode(nid))

            if ntype == INIT:
                if (get_type(getnode(nids[1])) == BOOL) or (get_type(getnode(nids[2])) == BOOL):
                    nodemap[nid] = EqualsOrIff(BV2B(getnode(nids[1])), BV2B(getnode(nids[2])))
                else:
                    nodemap[nid] = EqualsOrIff(getnode(nids[1]), getnode(nids[2]))
                initlist.append(getnode(nid))

            if ntype == CONSTRAINT:
                nodemap[nid] = BV2B(getnode(nids[0]))
                invarlist.append(getnode(nid))

            if ntype == BAD:
                nodemap[nid] = getnode(nids[0])
                invar_props.append(Not(BV2B(getnode(nid))))

            if nid not in nodemap:
                Logger.error("Unknown node type \"%s\""%ntype)

        if Logger.level(1):
            name = lambda x: str(nodemap[x]) if nodemap[x].is_symbol() else x
            uncovered = [name(x) for x in nodemap if x not in node_covered]
            uncovered.sort()
            if len(uncovered) > 0:
                Logger.warning("Unlinked nodes \"%s\""%",".join(uncovered))

        if not self.symbolic_init:
            init = simplify(And(initlist))
        else:
            init = TRUE()
        trans = simplify(And(translist))
        invar = simplify(And(invarlist))

        ts.set_behavior(init, trans, invar)
        hts.add_ts(ts)

        return (hts, invar_props, ltl_props)
