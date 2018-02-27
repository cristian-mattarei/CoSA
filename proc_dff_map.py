#!/usr/bin/env python3

'''
Reads a Yosys log file to map the original register names to the $procdff{id} naming scheme.
Hopefully will eventually add flag to Yosys for preserving names
'''

import argparse

parser = argparse.ArgumentParser(description='Read proc_dff mappings from yosys log')
parser.add_argument('log_filename', metavar='<LOG_FILE>', help='The Yosys log file to read')
parser.add_argument('output_filename', metavar='<OUTPUT_FILE>', help='File to write the mapping to')

args = parser.parse_args()

log_filename = args.log_filename
output_filename = args.output_filename

output = open(output_filename, "w")

with open(log_filename) as f:
    log = f.read()
    f.close()

reg_ind = "Creating register for signal `"
end_reg_ind = "'"
dff_ind = "created $dff cell `"
end_dff_ind = "'"

for line in log.split("\n"):
    if reg_ind in line:
        signame = line[line.find(reg_ind)+len(reg_ind):line.find(end_reg_ind)]
        signame = signame.replace("\\", "")
        signame = signame.replace("$", "__DOLLAR__")
    elif dff_ind in line:
        dffname = line[line.find(dff_ind)+len(dff_ind):line.find(end_dff_ind)]
        dffname = dffname.replace("\\", "")
        dffname = dffname.replace("$", "__DOLLAR__")
        output.write("{} : {}\n".format(signame, dffname))
    else:
        pass
