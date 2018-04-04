#!/usr/bin/env python3

'''
Reads a Yosys log file to map the original register names to the $procdff{id} naming scheme.
Hopefully will eventually add flag to Yosys for preserving names
'''

##
# CoreIR mangling: \ -> ''
#                  $ -> '__DOLLAR__'
# CoreIR flattening
#  top$pe_tile_name$sb_name$procdff<ID>
#  top$pe_tile_name$cb_name$procdff<ID>
# Tile naming scheme
#       PE          t0_row_col
#      Mem          t1_row_col
# CB naming scheme
#      cb_unq1      a/b   16bit PE inputs
#      cb_unq2      d/e/f 1bit  PE inputs
#      cb_unq3      wdata/waddr/raddr 16bit Mem inputs
#      cb_unq4      ren/wen 1bit Mem inputs
# SB naming scheme
#      sb_unq1      16bit PE and Mem signals
#      sb_unq2      1bit  PE and Mem signals
#
##

import argparse

reg_ind = "Creating register for signal `"
end_reg_ind = "'"
dff_ind = "created $dff cell `"
adff_ind = "created $adff cell `"
end_dff_ind = "'"

io_m = "IO "
s_m = "STATE "
ms_m = "MOD.SIG: "

def read_log_file(log_filename, statemap_filename):
    with open(log_filename) as f:
        log = f.read()
        f.close()

    with open(statemap_filename) as f:
        sm = f.read()
        f.close()

    procdff_mapping = {}

    for line in log.split("\n"):
        if reg_ind in line:
            signame = line[line.find(reg_ind)+len(reg_ind):line.find(end_reg_ind)]
            signame = signame.replace("\\", "")
        elif dff_ind in line or adff_ind in line:
            ind = dff_ind if dff_ind in line else adff_ind
            dffname = line[line.find(ind)+len(ind):line.find(end_dff_ind)]
            dffname = dffname.replace("\\", "")
            dffname = dffname.replace("$", "__DOLLAR__")
            procdff_mapping[signame] = dffname
        else:
            pass

    name_mapping = {}
    for line in sm.split("\n"):
        if io_m in line:
            mname = line[line.find(io_m)+len(io_m):line.find(":")]
            fabname = line[line.find(": ")+2:]
            name_mapping[mname] = fabname
        elif s_m in line:
            mname = line[line.find(s_m)+len(s_m):line.find(":")]
            fabname = line[line.find(": ")+2:line.find(ms_m)]
            mod_width_sig = line[line.find(ms_m)+len(ms_m):]
            mod, width, sig = mod_width_sig.split(".")
            # a little hacky
            # not sure how to anticipate paramod name in general
            paramodname = "$paramod{}DataWidth={}.{}".format(mod, width, sig)
            modsig = "{}.{}".format(mod,sig)
            # paramodname has priority
            if paramodname in procdff_mapping:
                procdffname = procdff_mapping[paramodname]
            elif modsig in procdff_mapping:
                procdffname = procdff_mapping[modsig]
            else:
                raise RuntimeError("Could not infer mapping from Yosys log.")
            fabname = fabname.replace(sig, procdffname)
            name_mapping[mname] = fabname.strip()

    return name_mapping

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Read proc_dff mappings from yosys log')
    parser.add_argument('log_filename', metavar='<LOG_FILE>', help='The Yosys log file to read')
    parser.add_argument('statemap_filename', metavar='<STATE_MAP_FILE>', help='The file produced from PNR with --state-map flag')
    parser.add_argument('output_filename', metavar='<OUTPUT_FILE>', help='File to write the mapping to')

    args = parser.parse_args()

    log_filename = args.log_filename
    statemap_filename = args.statemap_filename
    output_filename = args.output_filename

    nm = read_log_file(log_filename, statemap_filename)

    with open(output_filename, "w") as output:
        for k, v in nm.items():
            output.write("{}: {}\n".format(k, v))
        output.close()
