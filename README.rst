.. figure:: http://www.mattarei.eu/cristian/images/CoSA-logo_small.png
   :align: center
   
CoSA: CoreIR Symbolic Analyzer
========================

...an SMT-based symbolic model checker for hardware design. 

========================
Overview
========================

CoSA supports a variety of input formats:

- `CoreIR`_
- `BTOR2`_
- Verilog
- SystemVerilog
- Symbolic Transition System (`STS`_)
- Explicit states Transition System (`ETS`_)

and verifications:

- Invariant Properties
- Linear Temporal Logic (LTL) Properties
- Proving capabilities
- Equivalence Checking
- Parametric (Invariant) Model Checking
- Fault Analysis
- Automated Lemma Extraction

========================
Installation
========================

1) ``pip3 install cosa`` to install CoSA, and its dependencies i.e., `PySMT`_, `PyCoreIR`_, and `PyVerilog`_

2) ``pysmt-install --msat`` to install `MathSAT5`_ solver (it provides interpolation support), or ``pysmt-install --cvc4`` for `CVC4`_ and ``pysmt-install --z3`` for `Z3`_

3) ``pysmt-install --env`` to show the environment variables that need to be exported

Software requirements:

- `CoreIR`_ needs to be installed in order to support CoreIR as input format
- `Icarus Verilog`_ needs to be installed in order to support Verilog as input format
- `Verific`_ binaries (i.e., ``verific``) and `Icarus Verilog`_ need to be installed in order to support SystemVerilog as input format

.. _PyCoreIR: https://github.com/leonardt/pycoreir
.. _PySMT: https://github.com/pysmt/pysmt
.. _MathSAT5: http://mathsat.fbk.eu
.. _CVC4: http://cvc4.cs.stanford.edu/web/
.. _Z3: https://github.com/Z3Prover/z3

.. _CoreIR: https://github.com/rdaly525/coreir
.. _Icarus Verilog: https://github.com/steveicarus/iverilog
.. _PyVerilog: https://github.com/PyHDI/Pyverilog
.. _Verific: http://www.verific.com/
.. _BTOR2: https://github.com/Boolector/btor2tools
.. _STS: https://github.com/cristian-mattarei/CoSA/blob/master/doc/sts.rst
.. _ETS: https://github.com/cristian-mattarei/CoSA/blob/master/doc/ets.rst

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
License
========================

CoSA is released under the modified BSD (3-clause BSD) License.

If you use CoSA in your work, please consider citing the following publication:

.. code::

   @inproceedings{DBLP:conf/fmcad/MattareiMBDHH18,
     author    = {Cristian Mattarei and
                 Makai Mann and
                 Clark Barrett and
                 Ross G. Daly and
                 Dillon Huff and
                 Pat Hanrahan},
    title     = {{CoSA: Integrated Verification for Agile Hardware Design}},
    booktitle = {Formal Methods in Computer-Aided Design, {FMCAD} 2018, Austin, Texas,
                 USA, October 30 - November 2, 2018.},
    publisher = {{IEEE}},
    year      = {2018}
  }

========================
Build Status
========================

.. image:: https://travis-ci.org/cristian-mattarei/CoSA.svg?branch=master
    :target: https://travis-ci.org/cristian-mattarei/CoSA
