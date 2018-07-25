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
