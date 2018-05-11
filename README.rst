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

1) ``python3 CoSA.py -i examples/counters/counters.json --simulate -k 7`` (generates a system execution with depth 7)

2) ``python3 CoSA.py -i examples/counters/counters.json --safety -p "!(count0.a.out = 5_16)" -k 7`` (performs reachability model checking with property count0.a.out != 5 as a 16-bit Bitvector)

3) ``python3 CoSA.py --problem examples/counter/problem.txt --prefix trace`` (liveness (GF) and finally (F) checking on the counter.json model using the problem definition)

4) ``python3 CoSA.py --problem examples/fold-constants/problem.txt -v2`` (performs equivalence checking using lemmas)

========================
Docker
========================

1) install Docker with your package manager e.g., ``sudo apt-get install docker``

2) build the Docker image: ``cd docker/ubuntu_1604 && docker build -t ubuntu-cosa .``

3) run the Docker image: ``docker run -i -t ubuntu-cosa /bin/bash``
