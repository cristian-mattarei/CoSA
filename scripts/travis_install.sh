#!/bin/bash

# PYCOREIR="`pwd`/pycoreir/setup.py"
COREIR="`pwd`/coreir/build"

if [ ! -f "$COREIR" ]; then
    rm -fr coreir*
    wget https://github.com/rdaly525/coreir/archive/master.zip
    unzip master.zip
    rm master.zip
    mv coreir-master coreir
    cd coreir
    mkdir build
    cd build
    cmake ..
    make -j4 && sudo make install
    cd ../../
else
    echo "Skipping COREIR installation"
    cd coreir/build
    make -j4 && sudo make install
    cd ../../
fi

# # use latest master instead of release
# git clone https://github.com/leonardt/pycoreir.git
# cd pycoreir
# pip install cmake twine wheel pytest
# pip install -e .
# cd ../

# Get yosys -- using for verilog frontend
wget http://web.stanford.edu/~makaim/files/yosys.tar.xz
tar -xf yosys.tar.xz
