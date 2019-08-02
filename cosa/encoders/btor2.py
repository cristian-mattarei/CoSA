from pathlib import Path
from typing import Callable, Dict, List, NamedTuple, Set, Tuple, Union

from pysmt.exceptions import PysmtTypeError
from pysmt.fnode import FNode
from pysmt.shortcuts import Not, TRUE, And, BVNot, BVNeg, BVAnd, BVOr, BVAdd, Or, Symbol, BV, EqualsOrIff, \
    Implies, BVMul, BVExtract, BVUGT, BVUGE, BVULT, BVULE, BVSGT, BVSGE, BVSLT, BVSLE, \
    Ite, BVZExt, BVSExt, BVXor, BVConcat, get_type, BVSub, Xor, Select, Store, BVComp, simplify, \
    BVLShl, BVAShr, BVLShr, BVType, ArrayType
from pysmt.typing import PySMTType, BOOL

from cosa.encoders.template import ModelParser
from cosa.representation import HTS, TS
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import B2BV, BV2B

NL = "\n"
COLON_REP = "_c_"
SN="N%s"
COM=";"

STATE="state"
NEXT="next"
INIT="init"
INPUT="input"
OUTPUT="output"
BAD="bad"
CONSTRAINT="constraint"
JUSTICE="justice"

special_char_replacements = {"$": "", "\\": ".", ":": COLON_REP}

# BTOR2Converter is kept separate from the parser to keep all state-ful elements separate
# Thus, BTOR2Parser can be re-used for multiple BTOR files, but BTOR2Converter must be
# initialized each time
class BTOR2Converter:
    '''
    Class used to map BTOR operators to the equivalent PySMT functions

    Utilized by BTOR2Parser
    '''
    def __init__(self):
        self.hts = HTS()
        self.ts = TS()

        self.nodemap = {}
        self.node_covered = set()

        # list of tuples of var and cond_assign_list
        # cond_assign_list is tuples of (condition, value)
        # where everything is a pysmt FNode
        # for btor, the condition is always True
        self.ftrans = []
        self.initlist = []
        self.invarlist = []

        self.invar_props = []
        self.ltl_props = []

        # converter should only be used once
        self.converted = False

        #TODO: look into a more optimal way of passing arguments, constantly packing and unpacking tuples now

        # These btor operators take FNodes for every option
        # Thus the arguments are implicitly converted to FNodes first by looking up the id in the nodemap
        self.all_fnode_op_map = {
            "implies" : lambda p, q    : BTOR2Converter._apply_bool_op(Implies, p, q),
            "eq"      : lambda x, y    : BTOR2Converter._apply_bv_or_bool_op(BVComp, EqualsOrIff, x, y),
            "neq"     : lambda x, y    : BTOR2Converter._apply_bv_or_bool_op(BVComp, EqualsOrIff, x, y, negate=True),
            "and"     : lambda *args   : BTOR2Converter._apply_bv_or_bool_op(BVAnd, And, *args),
            "or"      : lambda *args   : BTOR2Converter._apply_bv_or_bool_op(BVOr, Or, *args),
            "xor"     : lambda *args   : BTOR2Converter._apply_bv_or_bool_op(BVXor, Xor, *args),
            "xnor"    : lambda *args   : BTOR2Converter._apply_bv_or_bool_op(BVXor, Xor, *args, negate=True),
            "nand"    : lambda *args   : BTOR2Converter._apply_bv_or_bool_op(BVAnd, And, *args, negate=True),
            "not"     : lambda a       : BTOR2Converter._apply_bv_or_bool_op(BVNot, Not, a),
            "neg"     : lambda a       : BTOR2Converter._apply_bv_or_bool_op(BVNeg, BTOR2Converter._identity, a),
            "add"     : lambda *args   : BTOR2Converter._apply_bv_op(BVAdd, *args),
            "sub"     : lambda *args   : BTOR2Converter._apply_bv_op(BVSub, *args),
            "ugt"     : lambda *args   : BTOR2Converter._apply_bv_op(BVUGT, *args),
            "ugte"    : lambda *args   : BTOR2Converter._apply_bv_op(BVUGTE, *args),
            "ult"     : lambda *args   : BTOR2Converter._apply_bv_op(BVULT, *args),
            "ulte"    : lambda *args   : BTOR2Converter._apply_bv_op(BVULTE, *args),
            "sgt"     : lambda *args   : BTOR2Converter._apply_bv_op(BVSGT, *args),
            "sgte"    : lambda *args   : BTOR2Converter._apply_bv_op(BVSGTE, *args),
            "slt"     : lambda *args   : BTOR2Converter._apply_bv_op(BVSLT, *args),
            "slte"    : lambda *args   : BTOR2Converter._apply_bv_op(BVSLTE, *args),
            "mul"     : lambda *args   : BTOR2Converter._apply_bv_op(BVMul, *args),
            "sll"     : lambda x, y    : BTOR2Converter._apply_bv_op(BVLShl, x, y),
            "sra"     : lambda x, y    : BTOR2Converter._apply_bv_op(BVAShr, x, y),
            "srl"     : lambda x, y    : BTOR2Converter._apply_bv_op(BVLShr, x, y),
            "concat"  : lambda *args   : BTOR2Converter._apply_bv_op(BVConcat, *args),
            "write"   : BTOR2Converter._store,
            "read"    : BTOR2Converter._select,
            "ite"     : BTOR2Converter._ite,
            "redor"   : BTOR2Converter._redor,
            "redand"  : BTOR2Converter._redand
        }

        # these btor operators interpret some of the arguments as integers
        self.mixed_op_map = {
            # PySMT uses [low:high] for slicing, aka Extract
            "slice"   : lambda s, x, h, l : BVExtract(B2BV(self.getnode(x)), int(l), int(h)),
            "uext"    : lambda s, x, w    : BVZExt(B2BV(self.getnode(x)), int(w)),
            "sext"    : lambda s, x, w    : BVSExt(B2BV(self.getnode(x)), int(w)),
            "zero"    : lambda s, w       : BV(0, int(w)),
            "one"     : lambda s, w       : BV(1, int(w)),
            "ones"    : lambda s, w       : BV((2**int(w))-1, int(w)),
            "constd"  : lambda s, a       : BV(int(a), self.getnode(s).width),
            "const"   : lambda s, a       : BV(int(a, 2), self.getnode(s).width),
            "consth"  : lambda s, a       : BV(int(a, 16), self.getnode(s).width),
            "sort"    : self._to_pysmt_type
        }

    def getnode(self, nid:str)->FNode:
        self.node_covered.add(nid)
        return self.nodemap[nid]

    def convert(self, lines:List[str], symbolic_init:bool)->Tuple[HTS, List[FNode], List[FNode]]:
        if self.converted:
            # converter should only be used once
            raise RuntimeError("Should not be calling convert more than once, construct a new object")

        for line in lines:
            linetok = line.split()
            if len(linetok) == 0:
                continue
            if linetok[0] == COM:
                continue

            (nid, ntype, *nids) = linetok

            # TODO: handle comments that occur on the same line
            exists_wirename = False
            # get wirenames for signals
            # unfortunately we need to create a new symbol for this -- e.g. there's no define-fun
            if ntype not in {STATE, INPUT, OUTPUT, BAD}:
                # check for wirename, if it's an integer, then it's a node ref not a wirename
                try:
                    a = int(nids[-1])
                except:
                    try:
                        wire = Symbol(str(nids[-1]), self.getnode(nids[0]))
                        exists_wirename = True
                        self.ts.add_var(wire)
                        nids = nids[:-1]
                    except:
                        pass

            self.process_line(nid, ntype, nids)

            if exists_wirename:
                self.invarlist.append(EqualsOrIff(wire, B2BV(self.nodemap[nid])))

        self.converted = True

        if Logger.level(1):
            def name(x):
                try:
                    n = self.nodemap[x]
                    if n.is_symbol():
                        return str(n)
                    else:
                        return x
                except:
                    return x

            uncovered = [name(x) for x in self.nodemap if x not in self.node_covered]
            uncovered.sort()
            if len(uncovered) > 0:
                Logger.warning("Unlinked nodes \"%s\""%",".join(uncovered))

        if not symbolic_init:
            init = simplify(And(self.initlist))
        else:
            init = TRUE()

        invar = simplify(And(self.invarlist))

        # instead of trans, we're using the ftrans format -- see below
        self.ts.set_behavior(init, TRUE(), invar)

        # add ftrans
        for var, cond_assign_list in self.ftrans:
            self.ts.add_func_trans(var, cond_assign_list)

        self.hts.add_ts(self.ts)

        return (self.hts, self.invar_props, self.ltl_props)


    def process_line(self, nid:str, ntype:str, nids:Tuple[str])->None:

        if ntype == STATE:
            if len(nids) > 1:
                self.nodemap[nid] = Symbol(nids[1], self.getnode(nids[0]))
            else:
                self.nodemap[nid] = Symbol((SN%nid), self.getnode(nids[0]))
            self.ts.add_state_var(self.nodemap[nid])

        elif ntype == NEXT:
            # state elements are never bool -- convert the righthand side if necessary
            lval = TS.get_prime(self.getnode(nids[1]))
            rval = self.getnode(nids[2])
            if rval.get_type().is_bool_type():
                rval = B2BV(rval)

            self.nodemap[nid] = EqualsOrIff(lval, rval)
            self.ftrans.append(
                (lval,
                 [(TRUE(), rval)])
            )

        elif ntype == INPUT:
            if len(nids) > 1:
                self.nodemap[nid] = Symbol(nids[1], self.getnode(nids[0]))
            else:
                self.nodemap[nid] = Symbol((SN%nid), self.getnode(nids[0]))
            self.ts.add_input_var(self.nodemap[nid])

        elif ntype == OUTPUT:
            # unfortunately we need to create an extra symbol just to have the output name
            # we could be smarter about this, but then this parser can't be greedy
            original_symbol = self.getnode(nids[0])
            output_symbol = Symbol(nids[1], original_symbol.get_type())
            self.nodemap[nid] = EqualsOrIff(output_symbol, original_symbol)
            self.invarlist.append(self.nodemap[nid])
            self.node_covered.add(nid)
            self.ts.add_output_var(output_symbol)

        elif ntype == INIT:
            nid1, nid2 = self.getnode(nids[1]), self.getnode(nids[2])
            if (get_type(nid1) == BOOL) or (get_type(nid2) == BOOL):
                node = EqualsOrIff(BV2B(nid1), BV2B(nid2))
            else:
                node = EqualsOrIff(nid1, nid2)
            self.nodemap[nid] = node
            self.initlist.append(node)

        elif ntype == CONSTRAINT:
            node = BV2B(getnode(nids[0]))
            self.nodemap[nid] = node
            self.invarlist.append(node)

        elif ntype == BAD:
            nodemap[nid] = getnode(nids[0])

            # Following problem format (name, description, strformula)
            self.invar_props.append((assert_name, description, Not(BV2B(self.getnode(nid)))))

        elif ntype == JUSTICE:
            raise RuntimeError("Justice (e.g. Buchi automata / liveness) properties are not yet supported for BTOR")

        elif ntype in self.all_fnode_op_map:
            # remove the first element because that's the sort
            # not necessary -- pysmt does its own type checking
            nids = [self.getnode(a) for a in nids[1:]]
            self.nodemap[nid] = self.all_fnode_op_map[ntype](*nids)

        elif ntype in self.mixed_op_map:
            self.nodemap[nid] = self.mixed_op_map[ntype](*nids)

        else:
            raise RuntimeError("Unhandled combinational BTOR op: {}".format(ntype))

    @staticmethod
    def _identity(a):
        return a

    def _to_pysmt_type(self, sort:str, *args)->PySMTType:
        if sort == "bitvec":
            return BVType(int(args[0]))
        elif sort == "array":
            return ArrayType(self.getnode(args[0]), self.getnode(args[1]))
        else:
            raise RuntimeError("Unsupported btor sort: {}".format(sort))

    @staticmethod
    def _apply_bv_or_bool_op(bv_op:Callable[...,FNode],
                             bool_op:Callable[...,FNode],
                             *args:FNode,
                             negate:bool=False
                             )->FNode:
        '''
        Applies a bit-vector or bool op, with preference for the bit-vector operator.
        '''
        _types = [a.get_type() for a in args]

        assert [t.is_bool_type() or t.is_bv_type() for t in _types], \
            "Expecting all booleans or all bv"

        num_bv_args = sum([t.is_bv_type() for t in _types])

        # preference for bit-vector operations
        if num_bv_args > len(_types)/2:
            return BTOR2Converter._apply_bv_op(bv_op, *args, negate=negate)
        else:
            return BTOR2Converter._apply_bool_op(bool_op, *args, negate=negate)

    @staticmethod
    def _apply_bv_op(bv_op:Callable[...,FNode], *args:FNode, negate:bool=False)->FNode:
        try:
            res = bv_op(*args)
        except (AssertionError, PysmtTypeError) as e:
            # cast to bv
            casted_args = [B2BV(a) for a in args]
            res = bv_op(*casted_args)

        if negate:
            res = BVNot(res)

        return res

    @staticmethod
    def _apply_bool_op(bool_op:Callable[...,FNode], *args:FNode, negate:bool=False)->FNode:
        try:
            res = bool_op(*args)
        except (AssertionError, PysmtTypeError) as e:
            # cast to bool
            casted_args = [BV2B(a) for a in args]
            res =  bool_op(*casted_args)

        if negate:
            res = Not(res)

        return res

    @staticmethod
    def _ite(c:FNode, a:FNode, b:FNode)->FNode:
        ct, at, bt = c.get_type(), a.get_type(), b.get_type()

        if not ct.is_bool_type():
            assert ct.is_bv_type() and ct.width == 1, "Expecting a bit-vector of size one if not a bool"
            c = EqualsOrIff(c, BV(1, 1))

        if at != bt:
            try:
                return Ite(c, B2BV(a), B2BV(b))
            except:
                raise ValueError("Couldn't correctly cast ite({}, {}, {})".format(c, a, b))
        else:
            return Ite(c, a, b)

    @staticmethod
    def _redor(arg:FNode)->FNode:
        width = get_type(arg).width
        zeros = BV(0, width)
        return BVNot(BVComp(arg, zeros))

    @staticmethod
    def _redand(arg:FNode)->FNode:
        width = get_type(arg).width
        ones = BV((2**width)-1, width)
        return BVComp(arg, ones)

    @staticmethod
    def _store(arr:FNode, idx:FNode, val:FNode)->FNode:
        try:
            return Store(arr, idx, val)
        except (AssertionError, PysmtTypeError) as e:
            _type = arr.get_type()
            assert _type.is_array_type(), "Expecting array type"

            idx_type, elem_type = idx.get_type(), val.get_type()
            arr_idx_type, arr_elem_type = _type.index_type, _type.elem_type

            if idx_type != arr_idx_type:
                if idx_type.is_bool_type() and arr_idx_type.is_bv_type():
                    idx = B2BV(idx)
                elif idx_type.is_bv_type() and arr_idx_type.is_bool_type():
                    idx = BV2B(idx)
                else:
                    raise RuntimeError("Can't cast {} to {}".format(idx, arr_idx_type))

            if elem_type != arr_elem_type:
                if elem_type.is_bool_type() and arr_elem_type.is_bv_type():
                    val = B2BV(val)
                elif elem_type.is_bv_type() and arr_elem_type.is_bool_type():
                    val = BV2B(val)
                else:
                    raise RuntimeError("Can't cast {} to {}".format(val, arr_elem_type))

            return Store(arr, idx, val)

    @staticmethod
    def _select(arr:FNode, idx:FNode)->FNode:
        try:
            return Select(arr, idx)
        except (AssertionError, PysmtTypeError) as e:
            _type = arr.get_type()
            assert _type.is_array_type(), "Expecting array type"

            idx_type, arr_idx_type = idx.get_type(), arr.index_type

            if idx_type.is_bool_type() and arr_idx_type.is_bv_type():
                idx = B2BV(idx)
            elif idx_type.is_bv_type() and arr_idx_type.is_bool_type():
                idx = BV2B(idx)
            else:
                raise RuntimeError("Can't cast {} to {}".format(idx, arr_idx_type))

            return Select(arr, idx)


class BTOR2Parser(ModelParser):
    parser = None
    extensions = ["btor2","btor"]
    name = "BTOR2"

    def __init__(self):
        pass

    def get_model_info(self):
        return None

    def parse_file(self,
                   filepath:Path,
                   config:NamedTuple,
                   flags:str=None)->Tuple[HTS, List[FNode], List[FNode]]:
        self.symbolic_init = config.symbolic_init
        with filepath.open("r") as f:
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

    def parse_string(self, strinput:str)->Tuple[HTS, List[FNode], List[FNode]]:
        converter = BTOR2Converter()

        # clean string input, remove special characters from names
        for sc, rep in special_char_replacements.items():
            strinput = strinput.replace(sc, rep)

        return converter.convert(strinput.split(NL), self.symbolic_init)
