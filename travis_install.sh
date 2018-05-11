pushd .

PYCOREIR="`pwd`/pycoreir"
if [ ! -f "$PYCOREIR" ]; then

    wget https://github.com/pysmt/pysmt/archive/15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
    unzip 15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
    rm 15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
    mv pysmt-15f039f8a2c84b5d8aea10b35d83d3c370b142b6 pysmt
    ls -lah
    cd pysmt
    pip3 install -e .
    pysmt-install --msat --confirm-agreement
    cd ..

    wget https://github.com/rdaly525/coreir/archive/a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
    unzip a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
    rm a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
    mv coreir-a20cb469a10f504ebed6ea8a1872bb5baac406c2 coreir
    cd coreir && make -j4 && make install
    cd ..

    wget https://github.com/leonardt/pycoreir/archive/0c10e7b814360d40b6291485fac7d921aae19d36.zip
    unzip 0c10e7b814360d40b6291485fac7d921aae19d36.zip
    rm 0c10e7b814360d40b6291485fac7d921aae19d36.zip
    mv pycoreir-0c10e7b814360d40b6291485fac7d921aae19d36 pycoreir
    cd pycoreir
    sed -i -e 's/KeyError(f"key={key} not found")/Error("key={key} not found".format(key=key))/g' coreir/type.py
    sed -i -e 's/KeyError(f"key={key} not in params={self.params.keys()}")/KeyError("key={key} not in params={params_keys}".format(key=key, params_keys=self.params.keys()))/g' coreir/generator.py
    sed -i -e 's/ValueError(f"Arg(name={key}, value={value}) does not match expected type {self.params\[key\].kind}")/ValueError("Arg(name={key}, value={value}) does not match expected type {params_kind}".format(key=key, value=value, params_kind=self.params\[key\].kind))/g' coreir/generator.py
    sed -i -e 's/f"{self.module.name}.{self.name}"/"{module_name}.{self_name}".format(module_name=self.module.name, name=self.name)/g' coreir/wireable.py
    pip3 install -e .

    popd

else
    echo "Skipping installation"

fi
