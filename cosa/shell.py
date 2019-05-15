#!/usr/bin/env python3

# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import sys
from typing import List, NamedTuple, Union

from pysmt.shortcuts import TRUE, FALSE

from cosa.analyzers.dispatcher import ProblemSolver, FILE_SP, MODEL_SP
from cosa.environment import reset_env
from cosa.options import cosa_option_manager
from cosa.printers.factory import HTSPrintersFactory
from cosa.problem import ProblemsManager, Trace, VerificationStatus, VerificationType
from cosa.utils.logger import Logger

TRACE_PREFIX = "trace"

def traces_printed(msg, trace_files):
    traces = ", and\n - ".join(["\"%s\""%f for f in trace_files])
    Logger.log("\n%s saved in:\n - %s"%(msg, traces), 0)

def print_traces(msg, traces, index, prefix, tracecount):
    trace_files = []
    trace_prefix = None

    i = 1
    for trace in traces:
        if prefix:
            trace_prefix = prefix
        else:
            if not trace.human_readable:
                trace_prefix = TRACE_PREFIX

        if trace_prefix:
            trace_file = "%s[%d]-%s.%s"%(trace_prefix, i, index, trace.extension)
            i+=1
            trace_files.append(trace_file)
            with open(trace_file, "w") as f:
                f.write(str(trace))

            if tracecount < 0:
                continue

        else:
            Logger.log("%s:"%(msg), 0)
            Logger.log(str(trace), 0)

    if (tracecount > 0) and (len(trace_files) > 0):
        traces_idx = ", ".join("[%s]"%(idx) for idx in range(tracecount, tracecount+len(traces), 1))
        Logger.log("%s%s: %s"%(msg, "s" if len(traces) > 1 else "", traces_idx), 0)
        tracelen = max(t.length for t in traces)
        Logger.log("Trace%s: %d"%("s (max) length" if len(traces) > 1 else " length", tracelen+1), 0)

    if (tracecount < 0) and (len(trace_files) > 0):
        traces_printed(msg, trace_files)
        return []

    return trace_files

def get_file_flags(strfile):
    if "[" not in strfile:
        return (strfile, [])

    (strfile, flags) = (strfile[:strfile.index("[")], strfile[strfile.index("[")+1:strfile.index("]")].split(FILE_SP))
    return (strfile, flags)

def translate(hts, config, formulae=None):
    # TODO: Fix this for the formulae which are not pysmt nodes at this point
    #       accessing the problem copy of it which is still a string
    Logger.log("\nWriting system to \"%s\""%(config.translate), 0)
    printer = HTSPrintersFactory.printer_by_name(config.printer)
    props = []
    if formulae is not None:
        for f in formulae:
            if f is None:
                continue
            assert isinstance(f, str), "Expecting strings from problem configuration"
            props.append(f)

    with open(config.translate, "w") as f:
        f.write(printer.print_hts(hts, props))

def print_problem_result(pbm:NamedTuple,
                         problems_config:ProblemsManager):

    status = problems_config.get_problem_status(pbm)
    if problems_config.has_problem_trace(pbm):
        traces = problems_config.get_problem_traces(pbm)
    else:
        traces = []
    general_config = problems_config.general_config
    count = len(traces) + 1
    if pbm.name is None:
        return (0, [])
    ret_status = 0

    unk_k = "" if status != VerificationStatus.UNK else "\nBMC depth: %s"%pbm.bmc_length
    Logger.log("\n** Problem %s **"%(pbm.name), 0)
    if pbm.description is not None:
        Logger.log("Description: %s"%(pbm.description), 0)
    if pbm.properties is not None:
        Logger.log("Formula: %s"%(pbm.properties), 1)
    Logger.log("Result: %s%s"%(status, unk_k), 0)
    if pbm.verification == VerificationType.PARAMETRIC:
        region = problems_config.get_problem_region(pbm)
        if region in [TRUE(),FALSE(),None]:
            Logger.log("Region: %s"%(region), 0)
        else:
            Logger.log("Region:\n - %s"%(" or \n - ".join([x.serialize(threshold=100) for x in region])), 0)
    if (pbm.expected is not None):
        expected = VerificationStatus.convert(pbm.expected)
        Logger.log("Expected: %s"%(expected), 0)
        correct = VerificationStatus.compare(VerificationStatus.convert(pbm.expected), status)
        if not correct:
            Logger.log("%s != %s <<<---------| ERROR"%(status, expected), 0)
            ret_status = 1

    assert not(general_config.force_expected and (pbm.expected is None))

    prefix = pbm.trace_prefix
    traces_results = []

    if (traces is not None) and (len(traces) > 0):
        if (pbm.verification == VerificationType.PARAMETRIC) and (status != VerificationStatus.FALSE):
            traces_results = print_traces("Execution", traces, pbm.name, prefix, count)

        if (pbm.verification != VerificationType.SIMULATION) and (status == VerificationStatus.FALSE):
            traces_results = print_traces("Counterexample", traces, pbm.name, prefix, count)

        if (pbm.verification == VerificationType.SIMULATION) and (status == VerificationStatus.TRUE):
            traces_results = print_traces("Execution", traces, pbm.name, prefix, count)

    if general_config.time:
        time = problems_config.get_problem_time(pbm)
        Logger.log("Time: %.2f sec"%(time), 0)

    return (ret_status, traces_results)

def run_problems(problems_config:ProblemsManager):

    if sys.version_info[0] < 3:
        if config.devel:
            Logger.warning("This software is not tested for Python 2, we recommend to use Python 3 instead")
        else:
            Logger.error("This software is not tested for Python 2, please use Python 3 instead. To avoid this error run in developer mode")

    reset_env()

    # Named tuple representing all the general configuration options
    # (things that don't change between problems)
    general_config = problems_config.general_config
    Logger.verbosity = general_config.verbosity
    Logger.time = general_config.time

    psol = ProblemSolver()
    psol.solve_problems(problems_config)

    global_status = 0
    traces = []

    if len(problems_config.problems) > 0:
        Logger.log("\n*** SUMMARY ***", 0)
    else:
        if not general_config.translate:
            Logger.log("No problems to solve", 0)
            return 0

    formulae = []
    for pbm in problems_config.problems:
        (status, trace) = print_problem_result(pbm,
                                               problems_config)

        if status != 0:
            global_status = status
        traces += trace
        formulae.append(pbm.properties)

    if len(traces) > 0:
        Logger.log("\n*** TRACES ***\n", 0)
        for trace in traces:
            Logger.log("[%d]:\t%s"%(traces.index(trace)+1, trace), 0)

    if general_config.translate:
        translate(problems_config.hts, general_config, formulae)

    if global_status != 0:
        Logger.log("", 0)
        Logger.warning("Verifications with unexpected result")

    return global_status

def main():

    problems_config = cosa_option_manager.parse_args()

    if len(sys.argv)==1:
        parser.print_help()
        sys.exit(1)

    sys.exit(run_problems(problems_config))

if __name__ == "__main__":
    main()
