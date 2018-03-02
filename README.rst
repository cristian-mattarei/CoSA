CoSA: CoreIR Symbolic Analyzer
========================



========================
Requirements
========================

1) pySMT: https://github.com/pysmt/pysmt

2) CoreIR: https://github.com/rdaly525/coreir/tree/dev (dev branch)

3) PyCoreIR: https://github.com/leonardt/pycoreir/tree/dev (dev branch)


========================
Usage
========================

To start playing with the tool, you can run:

1) ``python3 CoSA.py -i examples/counters.json --simulate -k 7`` (generates a system execution with depth 7)

2) ``python3 CoSA.py -i examples/counters.json --safety -p "!(count0.a.out = 5_16)" -k 7`` (performs reachability model checking with property count0.a.out != 5 with a 16-bit Bitvector)

3) ``python3 CoSA.py -i examples/mul_2_pe/system_1.json --equivalence examples/mul_2_pe/system_1.json -k 2`` (performs equivalence checking between system_1 and system2)

