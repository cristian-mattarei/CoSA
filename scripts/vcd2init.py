#!/usr/bin/env python3

import argparse
from collections import defaultdict, namedtuple
from pathlib import Path
import re
from typing import Any, Dict, List

VAR_EXTRACT_PATTERN = re.compile(r"(?P<name>.*)\[(?P<idx_high>\d+):(?P<idx_low>\d+)\]")
EXTRACT_PATTERN = re.compile(r"\[\d+:\d+\]")
MEM_PATTERN = re.compile(r"(?P<mem>.*)(?P<idx>\[\d+\])")
DELAY_PATTERN=re.compile(r"#\d+")

END    = "$end"
ENDDEF = "$enddefinitions"

bv = namedtuple('bv', 'val width')
var = namedtuple('var', 'type name size hier')

######################## helper functions for converting to pysmt #######################
def swap_indices(extract:str):
    '''
    Takes an extract operator, [digit0:digit1] and reverses the indices
    to [digit1:digit0]
    '''
    assert extract[0] == "["
    assert extract[-1] == "]"
    indices = extract[1:-1].split(":")
    assert len(indices) == 2
    return "[{}:{}]".format(indices[1], indices[0])

def remove_extract(var:str, size:int)->str:
    '''
    Takes a var with an extract and decides if the extract is the whole bit-vector.
    If so, it returns the string without the extract, otherwise it returns the input.
    '''
    m = re.match(VAR_EXTRACT_PATTERN, var)

    if not m:
        return var
    else:
        groupdict = m.groupdict()
        name = groupdict['name']
        idx_high = groupdict['idx_high']
        idx_low = groupdict['idx_low']

        try:
            idx_high = int(idx_high)
            idx_low = int(idx_low)
        except:
            raise RuntimeError("Expecting integers in extract but got {}, {}".format(idx_high, idx_low))

        if idx_low == 0 and idx_high == (size - 1):
            return name
        else:
            return var

def memacc(mem, idx):
    # unescape memories
    if mem[0] == '\\':
        mem = mem[1:]
    return "memacc({}, {})".format(mem, idx[1:-1])

def find_extracts(var:str):
    m = re.findall(EXTRACT_PATTERN, var)
    return m

def left_extend(val, size):
    '''
    Left-extends val if necessary, otherwise returns the input.
    '''

    len_val = len(val)

    if len_val == size:
        return val
    else:
        num_ext = size - len_val
        # if it's a one, we just prepend zeros because it's unsigned extension
        if val[0] == '1':
            val = "0"*num_ext + val
        # otherwise we extend the value
        else:
            val = val[0]*num_ext + val

        return val

def find_mems(var:str):
    m = re.findall(MEM_PATTERN, var)
    return m

def partition(val:str, key:Dict[Any, Any])->List[str]:
    idx_low = 0
    idx_high = 0

    gprev = key(val[-1])
    gcurr = None

    curr = val[-1]

    groups = {}

    for c in reversed(val[:-1]):
        gcurr = key(c)
        if gcurr == gprev:
            idx_high += 1
            curr = c + curr
        else:
            groups[gprev] = (idx_low, idx_high, curr)
            idx_high += 1
            idx_low = idx_high
            curr = c
        gprev = gcurr

    groups[gprev] = (idx_low, idx_high, curr)

    return groups

################################# end helper functions #########################################

################################# VCD Reading functions ########################################

def read_header(header:str, hiermod:str)->Dict[str, List[var]]:
    hier = []
    varmap = defaultdict(list)

    assert header[-len(ENDDEF):] == ENDDEF, \
        "expected {} but got {}".format(ENDDEF, header[-len(ENDDEF):])

    for line in header.split('\n'):
        if "$var" in line:
            _, _type, size, code, *rest = line.split()
            size = int(size)
            name = "".join(rest[:-1])
            # create hierarchical name
            name = "{}.{}".format('.'.join(hier), name)
            # strip leading hiermod -- the testbench modules, etc...
            name = name.replace(hiermod + '.', '', 1)
            name = remove_extract(name, size)
            # replace extracts with pysmt version -- [lsb:msb]
            for m in find_extracts(name):
                name = name.replace(m, swap_indices(m))
            for m in find_mems(name):
                assert len(m) == 2
                mem, idx = m
                memsel = mem + idx
                name = name.replace(memsel, memacc(mem, idx))
            varmap[code].append(var(_type, name, size, '.'.join(hier)))
        elif "$scope" in line:
            hier.append(line.split()[2])
        elif "$upscope" in line:
            hier.pop()

    return varmap

def get_last_state(contents:str, varmap:Dict[str, List[var]])->Dict[str, List[str]]:

    # expected inputs in value
    expected = {
        '0': 'val',
        '1': 'val',
        'X': 'unknown',
        'x': 'unknown',
        'Z': 'unknown',
        'z': 'unknown'
    }

    # groups for partition
    key = lambda x : expected[x] if x in expected else 'invalid'

    assignment = dict()

    for line in contents.split('\n'):
        line = line.strip()
        if not line:
            continue
        elif line[0] == "$":
            # command word that we're ignoring (identifier can contain $ but the value would come first)
            continue
        elif re.match(DELAY_PATTERN, line):
            continue
        else:
            vals = line.split()

            onebit = False
            if len(vals) == 1:
                assert len(vals[0]) == 2
                vals = list(vals[0])
                onebit = True

            assert len(vals) == 2, "Expecting value and tag, but got {}".format(vals)
            val, tag = vals

            if not onebit:
                assert val[0] == 'b', "Expecting a bit-vector"
                # get the size of the referenced variable
                size = varmap[tag][0].size
                val = left_extend(val[1:], size)

            p = partition(val, key)

            if 'invalid' in p:
                raise RuntimeError("Value {} contains invalid symbols".format(val))
            elif 'val' in p:
                assignment[tag] = p['val']

    return assignment


# TODO: Fix the function signature
def parse_vcd(filename:str, hiermod:str)->List[bv]:
    fn = Path(filename)

    header = None
    contents = None
    with fn.open() as f:
        contents = f.read()
        endd_idx = contents.find(ENDDEF) + len(ENDDEF)
        header = contents[:endd_idx]
        contents = contents[endd_idx:]
        contents = contents[contents.find(END)+len(END):]

    assert header is not None
    assert contents is not None
    varmap = read_header(header, hiermod)

    assignment = get_last_state(contents, varmap)

    processed = set()
    final_assignments = list()
    for tag, ext_val in assignment.items():
        var = None
        for v in varmap[tag]:
            if v.hier == hiermod or ('.' in v.hier and v.hier.split(".")[0] == hiermod):
                var = v
                break
        if var is None:
            continue

        assert var not in processed, "Expecting to process each var only once"
        processed.add(var)

        assert len(ext_val) == 3
        idx_low, idx_high, val = ext_val
        width = idx_high - idx_low + 1
        pysmt_val = "{}_{}".format(int(val, 2), width)
        final_assignments.append("{}[{}:{}] = {}".format(var.name, idx_low, idx_high, pysmt_val))

    return final_assignments

################################# end VCD Reading functions ####################################

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='read a VCD file')
    parser.add_argument('vcd_file', help='the vcd file to read')
    parser.add_argument('--hiermod', '-t', required=True,
                        help='The hierarchical location of the module of interest')
    parser.add_argument('--output', '-o', default='cosa.init',
                        help='The name of the CoSA .init file to produce')

    args = parser.parse_args()

    hiermod = args.hiermod

    assignments = parse_vcd(args.vcd_file, hiermod)
    num_assignments = len(assignments)

    with open(args.output, 'w') as f:
        f.write("\n".join(assignments))
        f.write("\n")

    print("Wrote {} initial values to {}".format(num_assignments, args.output))
