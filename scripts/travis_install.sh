#!/bin/bash

PYCOREIR="`pwd`/pycoreir/setup.py"
COREIR="`pwd`/coreir/Makefile"
PYSMT="`pwd`/pysmt/setup.py"
BITVECTOR="`pwd`/bit_vector/setup.py"

if [ ! -f "$PYSMT" ]; then
    rm -fr pysmt*
    wget https://github.com/pysmt/pysmt/archive/master.zip
    unzip master.zip
    rm master.zip
    mv pysmt-master pysmt
    cd pysmt
    pip3 install -e .
    pysmt-install --msat --confirm-agreement --install-path solvers --bindings-path bindings
    cd ..
else
    echo "Skipping PYSMT installation"
    cd pysmt && pip3 install -e . && cd ..
fi
    
export COREIRCONFIG="g++-4.9"

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
    cd coreir && sudo make install && cd ..
fi

if [ ! -f "$BITVECTOR" ]; then
    rm -fr bit_vector*
    wget https://github.com/leonardt/bit_vector/archive/320f1637271635840bade21c064cd011b740bdda.zip
    unzip 320f1637271635840bade21c064cd011b740bdda.zip
    rm 320f1637271635840bade21c064cd011b740bdda.zip
    mv bit_vector-320f1637271635840bade21c064cd011b740bdda bit_vector
    cd bit_vector
    sed -i -e 's/f"BitVector({self._value}, {self.num_bits})"/"BitVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
    sed -i -e 's/f"UIntVector({self._value}, {self.num_bits})"/"UIntVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
    sed -i -e 's/f"SIntVector({self._value}, {self.num_bits})"/"SIntVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
    pip3 install -e .
else
    echo "Skipping BIT_VECTOR installation"
    cd bit_vector && pip3 install -e . && cd ..
fi

if [ ! -f "$PYCOREIR" ]; then
    rm -fr pycoreir*
    wget https://github.com/leonardt/pycoreir/archive/master.zip
    unzip master.zip
    rm master.zip
    mv pycoreir-master pycoreir
    cd pycoreir
    sed -i -e 's/KeyError(f"key={key} not found")/Error("key={key} not found".format(key=key))/g' coreir/type.py
    sed -i -e 's/KeyError(f"key={key} not in params={self.params.keys()}")/KeyError("key={key} not in params={params_keys}".format(key=key, params_keys=self.params.keys()))/g' coreir/generator.py
    sed -i -e 's/ValueError(f"Arg(name={key}, value={value}) does not match expected type {self.params\[key\].kind}")/ValueError("Arg(name={key}, value={value}) does not match expected type {params_kind}".format(key=key, value=value, params_kind=self.params\[key\].kind))/g' coreir/generator.py
    sed -i -e 's/f"{self.module.name}.{self.name}"/"{module_name}.{self_name}".format(module_name=self.module.name, name=self.name)/g' coreir/wireable.py
    sed -i -e 's/f"Cannot select path {field}"/"Cannot select path {field}".format(field=field)/g' coreir/module.py
    pip3 install -e .
else
    echo "Skipping PYCOREIR installation"
    cd pycoreir && pip3 install -e . && cd ..
fi

