CoSA: CoreIR Symbolic Analyzer
========================


========================
Installation
========================

1) ``pip3 install cosa`` to install CoSA, and its dependencies i.e., `PyCoreIR`_, and `PySMT`_

.. _PyCoreIR: https://github.com/leonardt/pycoreir
.. _PySMT: https://github.com/pysmt/pysmt

2) ``pysmt-install --msat`` to install MathSAT5 solver (it provides interpolation support), or ``pysmt-install --cvc4/z3`` for other solvers

3) ``pysmt-install --env`` to show the environment variables that need to be exported

- `CoreIR`_ needs to be installed in order to support it as input format
.. _CoreIR: https://github.com/rdaly525/coreir

========================
Usage
========================

To start playing with the tool, you can run:

0) ``CoSA -h`` shows the helper with command options

1) ``CoSA -i examples/counters/counters.json --simulate -k 7`` generates a system execution with depth 7

2) ``CoSA -i examples/counters/counters.json --safety -p "!(count0.a.out = 5_16)" -k 7`` performs reachability model checking with property count0.a.out != 5 as a 16-bit Bitvector

3) ``CoSA --problem examples/counter/problem.txt --prefix trace`` performs liveness (GF) and finally (F) checking on the counter.json model using the problem definition

4) ``CoSA --problem examples/fold-constants/problem.txt`` performs equivalence checking using lemmas

========================
Docker
========================

1) install Docker with your package manager e.g., ``sudo apt-get install docker``

2) build the Docker image: ``cd docker/ubuntu_1604 && docker build -t ubuntu-cosa .``

3) run the Docker image: ``docker run -i -t ubuntu-cosa /bin/bash``

========================
Development
========================

- ``pip3 install -e .`` to install CoSA from the source
  
- ``nosetests tests`` to run the tests
   
========================
Build Status
========================

.. image:: https://travis-ci.org/cristian-mattarei/CoSA.svg?branch=master
    :target: https://travis-ci.org/cristian-mattarei/CoSA
