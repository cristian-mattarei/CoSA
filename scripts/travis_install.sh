#!/bin/bash

PYCOREIR="`pwd`/pycoreir/setup.py"
COREIR="`pwd`/coreir/Makefile"
PYSMT="`pwd`/pysmt/setup.py"
BITVECTOR="`pwd`/bit_vector/setup.py"

if [ ! -f "$PYSMT" ]; then
    rm -fr pysmt*
    # TEMP PySMT currently errors out upstream
    git clone -b cosa https://github.com/makaimann/pysmt.git
    # wget https://github.com/pysmt/pysmt/archive/master.zip
    # unzip master.zip
    # rm master.zip
    # mv pysmt-master pysmt
    cd pysmt
    pip3 install -e .
    pysmt-install --msat --confirm-agreement --install-path solvers --bindings-path bindings
    cd ..
else
    echo "Skipping PYSMT installation"
    cd pysmt && pip3 install -e . && cd ..
fi

if [ ! -f "$COREIR" ]; then
    rm -fr coreir*
    wget https://github.com/rdaly525/coreir/archive/master.zip
    unzip master.zip
    rm master.zip
    mv coreir-master coreir
    cd coreir && make -j4 && sudo make install
    cd ..
else
    echo "Skipping COREIR installation"
    cd pycoreir && pip install -e . && cd ..
fi

# don't need yosys for now
# wget http://web.stanford.edu/~makaim/files/yosys
# export PATH=`pwd`
