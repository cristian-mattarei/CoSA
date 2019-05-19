# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import datetime

from six.moves import cStringIO

from pysmt.shortcuts import BOOL

from cosa.representation import TS
from cosa.encoders.coreir import SEP
from cosa.utils.generic import dec_to_bin, dec_to_hex, sort_system_variables
from cosa.printers.template import TracePrinter, TraceValuesBase
from cosa.problem import Trace

NL = "\n"
VCD_SEP = "-"

PRE_TRACE = "---> "
POS_TRACE = " <---"
STATE = "STATE"

ALLIDX = "all"

def revise_abstract_clock(model, abstract_clock_list):
    newmodel = {}
    abs_clock = dict(abstract_clock_list)
    length = 0
    for var, value in model.items():
        refvar = TS.get_ref_var(var)
        time = TS.get_time(var)

        if time > 0:
            if refvar not in abs_clock:
                newmodel[TS.get_timed(refvar, (time*2)-1)] = value
                newmodel[TS.get_timed(refvar, (time*2))] = value
            else:
                newmodel[TS.get_timed(refvar, (time*2)-1)] = abs_clock[refvar][1]
                if value == abs_clock[refvar][1]:
                    newmodel[TS.get_timed(refvar, (time*2))] = abs_clock[refvar][0]
                else:
                    newmodel[TS.get_timed(refvar, (time*2))] = abs_clock[refvar][1]
                if ((time*2)+1) > length:
                    length = ((time*2))
        else:
            if refvar not in abs_clock:
                newmodel[TS.get_timed(refvar, 0)] = value
            else:
                newmodel[TS.get_timed(refvar, 0)] = abs_clock[refvar][0]

    return (newmodel, length)

class TextTracePrinter(TracePrinter):

    def __init__(self):
        self.prop_vars = None
        self.diff_only = True
        self.all_vars = False
        self.values_base = TraceValuesBase.HEX

    def get_file_ext(self):
        return "txt"

    def print_trace(self, hts, model, length, map_function=None, find_loop=False, abstract_clock_list=None):
        abstract_clock = (abstract_clock_list is not None) and (len(abstract_clock_list) > 0)
        if abstract_clock:
            (model, length) = revise_abstract_clock(model, abstract_clock_list)

        trace = []
        prevass = []

        # Initial state printing
        trace.append("%sINIT%s"%(PRE_TRACE, POS_TRACE))

        if self.all_vars:
            varlist = list(hts.vars)
        else:
            varlist = list(hts.input_vars.union(hts.output_vars))
            if self.prop_vars is not None:
                varlist = list(set(varlist).union(set(self.prop_vars)))

        strvarlist = [(map_function(var[0]), var[1]) for var in sort_system_variables(varlist, True) if not self.is_hidden(var[0])]

        for var in strvarlist:
            var_0 = TS.get_timed(var[1], 0)
            if var_0 not in model:
                prevass.append((var[0], None))
                continue
            varass = (var[0], model[var_0])
            if (self.values_base == TraceValuesBase.HEX) and (var[1].symbol_type().is_bv_type()):
                varass = (varass[0], "%d'h%s"%(var[1].symbol_type().width, dec_to_hex(varass[1].constant_value(), int(var[1].symbol_type().width/4))))
            if (self.values_base == TraceValuesBase.BIN) and (var[1].symbol_type().is_bv_type()):
                varass = (varass[0], "%d'b%s"%(var[1].symbol_type().width, dec_to_bin(varass[1].constant_value(), int(var[1].symbol_type().width))))
            if self.diff_only: prevass.append(varass)
            trace.append("  I: %s = %s"%(varass[0], varass[1]))

        if self.diff_only: prevass = dict(prevass)

        # Success state printing

        for t in range(length):
            trace.append("\n%s%s %d%s"%(PRE_TRACE, STATE, t+1, POS_TRACE))

            for var in strvarlist:
                var_t = TS.get_timed(var[1], t+1)
                if var_t not in model:
                    continue
                varass = (var[0], model[var_t])
                if (self.values_base == TraceValuesBase.HEX) and (var[1].symbol_type().is_bv_type()):
                    varass = (varass[0], "%d'h%s"%(var[1].symbol_type().width, dec_to_hex(varass[1].constant_value(), int(var[1].symbol_type().width/4))))
                if (self.values_base == TraceValuesBase.BIN) and (var[1].symbol_type().is_bv_type()):
                    varass = (varass[0], "%d'b%s"%(var[1].symbol_type().width, dec_to_bin(varass[1].constant_value(), int(var[1].symbol_type().width))))
                if (not self.diff_only) or (prevass[varass[0]] != varass[1]):
                    trace.append("  S%s: %s = %s"%(t+1, varass[0], varass[1]))
                    if self.diff_only: prevass[varass[0]] = varass[1]

        if find_loop:
            last_state = [(var[0], model[TS.get_timed(var[1], length)]) for var in strvarlist]
            last_state.sort()
            loop_id = -1
            for i in range(length):
                state_i = [(var[0], model[TS.get_timed(var[1], i)]) for var in strvarlist]
                state_i.sort()
                if state_i == last_state:
                    loop_id = i
                    break
            if loop_id >= 0:
                end = ("STATE %s"%loop_id) if loop_id > 0 else "INIT"
                trace.append("\n---> %s (Loop) <---"%(end))

        strtrace = NL.join(trace)
        trace = Trace(strtrace, length)
        trace.human_readable = True
        return trace

class VCDTracePrinter(TracePrinter):

    hierarchical = True

    def __init__(self):
        self.all_vars = False

    def get_file_ext(self):
        return "vcd"

    def print_trace(self, hts, model, length, map_function=None, abstract_clock_list=None):
        abstract_clock = (abstract_clock_list is not None) and (len(abstract_clock_list) > 0)

        if abstract_clock:
            (model, length) = revise_abstract_clock(model, abstract_clock_list)

        ret = []

        ret.append("$date")
        ret.append(datetime.datetime.now().strftime('%A %Y/%m/%d %H:%M:%S'))
        ret.append("$end")
        ret.append("$version")
        ret.append("CoSA")
        ret.append("$end")
        ret.append("$timescale")
        ret.append("1 ns")
        ret.append("$end")

        def _recover_array(array_model):
            # arrays are represented as a tuple of FNodes with
            # (previous, key, value, key, value, ...)
            # where previous can itself be another array
            args = array_model.args()
            # populate a stack of values to process
            stack = []
            while len(args) > 1:
                assert len(args)%2 == 1
                stack.append(args[1:])
                if not args[0].is_constant():
                    args = args[0].args()
                else:
                    args = [args[0]]
                    break

            symbolic_default = args[0]
            if symbolic_default.get_type().is_array_type():
                symbolic_default = symbolic_default.array_value_default()
                if symbolic_default.get_type().is_array_type():
                    Logger.error("Nested arrays are not supported in VCD output yet")

            assert symbolic_default.is_constant()
            default_val = symbolic_default.constant_value()

            assignments = dict()
            while stack:
                args = stack.pop()
                for a, v in zip([a.constant_value() for a in args[0::2]],
                                [v.constant_value() for v in args[1::2]]):
                    assignments[a] = v

            if self.all_vars:
                assignments[ALLIDX] = default_val
            return assignments

        model = dict([(v.symbol_name(), model[v].constant_value()
                          if not v.symbol_type().is_array_type()
                          else _recover_array(model[v])) for v in model])

        # These are the pysmt array vars
        arr_vars = list(filter(lambda v: v.symbol_type().is_array_type(), hts.vars))

        # Figure out which indices are used over all time
        arr_used_indices = {}
        for av in arr_vars:
            name = av.symbol_name()
            indices = set()
            for t in range(length+1):
                tname = TS.get_timed_name(map_function(name), t)
                if tname in model:
                    indices |= set((k for k in model[tname] if k != ALLIDX))
            arr_used_indices[name] = indices

        # These are the vcd vars (Arrays get blown out)
        varlist = []
        arr_varlist = []
        idvar = 0
        var2id = {}
        for v in sort_system_variables(hts.vars):
            n = map_function(v.symbol_name())
            if self.is_hidden(v.symbol_name()):
                continue
            if v.symbol_type() == BOOL:
                varlist.append((n, 1))
                var2id[n] = idvar
                idvar += 1
            elif v.symbol_type().is_bv_type():
                varlist.append((n, v.symbol_type().width))
                var2id[n] = idvar
                idvar += 1
            elif v.symbol_type().is_array_type():
                idxtype = v.symbol_type().index_type
                elemtype = v.symbol_type().elem_type
                if self.all_vars and idxtype.is_bv_type():
                    idxrange = range(2**idxtype.width)
                else:
                    idxrange = arr_used_indices[n]
                for idx in idxrange:
                    indexed_name = n + "[%i]"%idx
                    arr_varlist.append((indexed_name, elemtype.width))
                    var2id[indexed_name] = idvar
                    idvar += 1
            else:
                Logger.error("Unhandled type in VCD printer")

        for el in varlist + arr_varlist:
            (varname, width) = el
            idvar = var2id[varname]

            if self.hierarchical:
                varname = varname.split(SEP)
                for scope in varname[:-1]:
                    ret.append("$scope module %s $end"%scope)

                ret.append("$var reg %d v%s %s[%d:0] $end"%(width, idvar, varname[-1], width-1))

                for scope in range(len(varname)-1):
                    ret.append("$upscope $end")
            else:
                varname = varname.replace(SEP, VCD_SEP)
                ret.append("$var reg %d v%s %s[%d:0] $end"%(width, idvar, varname, width-1))


        ret.append("$upscope $end")
        ret.append("$upscope $end")
        ret.append("$enddefinitions $end")

        for t in range(length+1):
            ret.append("#%d"%t)
            for el in varlist:
                (varname, width) = el
                tname = TS.get_timed_name(varname, t)
                val = model[tname] if tname in model else 0
                ret.append("b%s v%s"%(dec_to_bin(val, width), var2id[varname]))

            for a in arr_vars:
                name = a.symbol_name()
                width = a.symbol_type().elem_type.width
                tname = TS.get_timed_name(name, t)
                if self.all_vars:
                    m = model[tname]
                    for i in set(range(2**a.symbol_type().index_type.width)) - m.keys():
                        vcdname = name + "[%i]"%i
                        ret.append("b%s v%s"%(dec_to_bin(m[ALLIDX],width),var2id[vcdname]))
                    del m[ALLIDX]
                    for i, v in m.items():
                        vcdname = name + "[%i]"%i
                        ret.append("b%s v%s"%(dec_to_bin(v,width),var2id[vcdname]))
                elif tname in model:
                    for i, v in model[tname].items():
                        vcdname = name + "[%i]"%i
                        ret.append("b%s v%s"%(dec_to_bin(v,width),var2id[vcdname]))

        # make the last time step visible
        # also important for correctness, gtkwave sometimes doesn't read the
        # last timestep's values correctly without this change
        ret.append("#%d"%(t+1))

        return Trace(NL.join(ret), length)
