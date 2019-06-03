# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import math
import os
import sys
import tempfile

from typing import Sequence, Union

STRING_PATTERN = "___STRING_%d___"
string_id = 0

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

def status_bar(status, percent=True, length=40):
    curr = math.ceil(length*status)
    percent = (" %.2f%%"%(status*100)) if percent else ""
    return "["+("#"*(curr))+(" "*(length-curr))+"]"+percent

def dec_to_bin(val, width):
    bitval = "{0:b}".format(int(val))
    bitval = "%s%s"%("0"*(width-len(bitval)), bitval)
    return bitval

def dec_to_hex(val, width):
    hexval = str(hex(val))[2:]
    hexval = "%s%s"%("0"*(width-len(hexval)), hexval)
    return hexval.upper()

def bin_to_dec(val):
    return int(val, 2)

def new_string():
    global string_id

    string_id += 1
    return STRING_PATTERN%string_id

def suppress_output(redirect_error=False):
    tmpfile = open(tempfile.mktemp(), "w")

    oldstdout = os.dup(1)
    os.dup2(tmpfile.fileno(), 1)
    oldstderr = None
    if redirect_error:
        oldstderr = os.dup(2)
        os.dup2(tmpfile.fileno(), 2)
    return (tmpfile, oldstdout, oldstderr)

def restore_output(saved_status):
    (tmpfile, old_stdout, old_stderr) = saved_status
    os.dup2(old_stdout, 1)
    if old_stderr is not None:
        os.dup2(old_stderr, 2)
    tmpfile.close()

def check_command(cmd):
    retval = os.system(cmd)
    return (retval == 0)

def sort_system_variables(variables, with_names=False):
    depthdic = {}
    maxdepth = 0
    for v in variables:
        varname = v.symbol_name()
        depth = len(varname.split("."))
        if depth > maxdepth:
            maxdepth = depth
        if depth not in depthdic:
            depthdic[depth] = []
        depthdic[depth].append((varname, v))

    ret = []
    depths = list(depthdic.keys())
    depths.sort()

    for i in depths:
        vars = depthdic[i]
        vars.sort()
        if with_names:
            ret += [v for v in depthdic[i]]
        else:
            ret += [v[1] for v in depthdic[i]]
    assert len(ret) == len(variables)
    return ret

def class_name(obj):
    return obj.__class__.__name__

class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   BOLD = '\033[1m'
   UNDERLINE = '\033[4m'
   END = '\033[0m'

def bold_text(text):
    return color.BOLD + text + color.END

def simple_struct(name:str, fields:Union[str, Sequence[str]]):
    '''
    Constructs a simple (mutable) struct class with the given fields

    Supports any sequence of strings, or the namedtuple-style single
    space-delimited string, e.g. 'field1 field2 field3'
    '''

    if isinstance(fields, str):
        fields = fields.split()

    class generated_simple_struct:
        __slots__ = fields
        def __init__(self, *args, **kwargs):
            unknown_kwargs = kwargs.keys() - fields
            assert len(unknown_kwargs) == 0, "unknown fields {}".format(unknown_kwargs)

            positional_args = generated_simple_struct.__slots__[:len(args)]
            overlapping_args = set(kwargs.keys()).intersection(positional_args)
            assert len(overlapping_args) == 0, \
                "Got two values for the following field(s) {}".format(overlapping_args)

            for f, v in zip(positional_args, args):
                setattr(self, f, v)

            for k, v in kwargs.items():
                setattr(self, k, v)

        def _get_assignments(self):
            str_assignments = ['{}={}'.format(f, getattr(self, f)) for f in generated_simple_struct.__slots__]
            return ", ".join(str_assignments)

        def __repr__(self):
            return "{}({})".format(name, self._get_assignments())

        def __str__(self):
            return "{}({})".format(name, self._get_assignments())

        def keys(self):
            return generated_simple_struct.__slots__

        def __getitem__(self, key):
            return getattr(self, key)

        def _asdict(self):
            return {f:getattr(self, f) for f in generated_simple_struct.__slots__}

    return generated_simple_struct
