# Copyright 2018 Cristian Mattarei, Makai Mann, Stanford University
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import BV, get_type, get_free_variables
from pysmt.shortcuts import  BVExtract, BVAdd, BVLShl, BVMul, BVZExt
from pysmt.fnode import FNode

from cosa.utils.logger import Logger

# Verilog defaults to size 32 bit vectors
DEFAULTINT = 32

# TODO: Complete this, might need a walker? Because can't just tell from top op, could be a plus or multiply or something
def signed(v):
    '''
    Checks if this is a signed bit-vector constant, symbol or op
    '''
    raise NotImplementedError

def vlog_match_widths(left, right, extend=False):
    '''
    Match the bit-widths for assignment using the Verilog standard semantics.

    if extend:
       zero extend to largest width
    else:
       left_width == right_width: no change
       left_width > right_width: right side is zero extended or sign extended depending on signedness
       left_width < right_width: right side is truncated (MSBs removed)
    '''
    assert type(left) == FNode and get_type(left).is_bv_type(), "Expecting a bit-vector"
    assert type(right) == FNode and get_type(right).is_bv_type(), "Expecting a bit-vector"

    left_width, right_width = left.bv_width(), right.bv_width()

    if left_width == right_width:
        return left, right
    elif left_width > right_width:
        # TODO: Check signed-ness of right-side

        fun = None
        padding = 0

        # handle ops with overflow:
        if right.is_bv_add():
            fun = BVAdd
            padding = 1
        elif right.is_bv_mul():
            fun = BVMul
            padding = 1
        elif right.is_bv_lshl():
            fun = BVLShl
            padding = left_width - right_width

        assert padding >= 0, "Expecting a non-negative padding"

        # TODO: Handle signed values here as well
        # re-build the node
        if padding > 0:
            args = [BVZExt(a, padding) for a in right.args()]
            right = fun(*args)

        # re-evauluate left_width and right_width, in case they're updated
        left_width, right_width = left.bv_width(), right.bv_width()

        assert left_width >= right_width, "Unexpected bitwidth mismatch"

        if left_width > right_width:
            right = BVZExt(right, left_width-right_width)

        return left, right
    else:
        if extend:
            return BVZExt(left, right_width-left_width), right
        else:
            return left, BVExtract(right, 0, left_width-1)

def get_const(val, match=None):
    '''
    Returns a bit-vector constant based on the input value.

    If match is an FNode instead of None, tries to match the bit-width
    '''
    if type(val) == FNode:
        return val
    elif type(val) == int:
        if match is not None:
            if type(match) != FNode:
                Logger.error("Expecting an FNode in get_const, but got {}".format(type(match)))
            match_width = get_type(match).width
            if val.bit_length() > match_width:
                Logger.error("Trying to match bit-width of {} but can't express {} in {} bits".format(match, val, match_width))
            return BV(val, match_width)
        return BV(val, DEFAULTINT)
    else:
        raise RuntimeError("Unhandled case in get_const: {}".format(type(val)))
