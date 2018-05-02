#!/usr/bin/env python3

import coreir
import argparse

CR = "_const_replacement"
RCR = "_reg_const_replacement"

def produce_fold_constants_conditions(libs, strfile):
    context = coreir.Context()
    for lib in libs:
        context.load_library(lib)

    top = context.load_from_file(strfile)
    td = top.definition

    folded_consts = []

    def _get_info(inst):
        # Create dictionary out of CoreIR Record
        assert "value" in inst.config
        val = inst.config["value"].value

        if type(val) == bool:
            strval = "1_1" if val else "0_1"
        else:
            if type(val) != int:
                val = val.val

            assert "width" in inst.config
            width = inst.config["width"].value
            strval = "{}_{}".format(val, width)

        return strval

    # assuming input is flattened
    for inst in td.instances:
        name = inst.selectpath[0]
        if "const" not in inst.module.name:
            continue
        elif len(name) > len(RCR) and name[-len(RCR):] == RCR:
            strval = _get_info(inst)
            folded_consts.append("({}.out = {})".format(name.replace(RCR,""), strval))
        elif len(name) > len(CR) and name[-len(CR):] == CR:
            strval = _get_info(inst)
            folded_consts.append("({}.out = {})".format(name.replace(CR,""), strval))

    return folded_consts

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Produce properties file for side conditions of fold_constants pass verification\nUses naming convention '_const_replacement'")
    parser.add_argument('input_file', metavar='<INPUT_FILE>', help='The filename of the flattened coreir after running fold-constants')
    parser.add_argument('output_file', metavar='<OUTPUT_FILE>', help='The filename to write the properties to')
    args = parser.parse_args()

    input_file = args.input_file
    output_file = args.output_file

    fc = produce_fold_constants_conditions([], input_file)

    with open(output_file, "w") as f:
        f.write(" & ".join(fc))
        f.close()
