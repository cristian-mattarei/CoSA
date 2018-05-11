FROM ubuntu:18.04
WORKDIR /home/CoSA

RUN apt-get update
RUN apt-get install -y python3-pip libpcre* wget unzip build-essential python3 automake libgmp-dev curl nano python3-dev libboost-dev default-jdk libclang-dev llvm llvm-dev lbzip2 libncurses5-dev git libtool

RUN wget https://github.com/pysmt/pysmt/archive/15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
RUN unzip 15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
RUN rm 15f039f8a2c84b5d8aea10b35d83d3c370b142b6.zip
RUN mv pysmt-15f039f8a2c84b5d8aea10b35d83d3c370b142b6 pysmt
RUN cd pysmt && pip3 install -e .
RUN pysmt-install --msat --confirm-agreement
ENV PYTHONPATH="/root/.smt_solvers/python-bindings-3.6:${PYTHONPATH}"
ENV LD_LIBRARY_PATH="/root/.smt_solvers/python-bindings-3.6:${LD_LIBRARY_PATH}"

RUN wget https://github.com/rdaly525/coreir/archive/a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
RUN unzip a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
RUN rm a20cb469a10f504ebed6ea8a1872bb5baac406c2.zip
RUN mv coreir-a20cb469a10f504ebed6ea8a1872bb5baac406c2 coreir
RUN cd coreir && make -j4 && make install

RUN wget https://github.com/leonardt/pycoreir/archive/0c10e7b814360d40b6291485fac7d921aae19d36.zip
RUN unzip 0c10e7b814360d40b6291485fac7d921aae19d36.zip
RUN rm 0c10e7b814360d40b6291485fac7d921aae19d36.zip
RUN mv pycoreir-0c10e7b814360d40b6291485fac7d921aae19d36 pycoreir
RUN cd pycoreir && sed -i -e 's/KeyError(f"key={key} not found")/Error("key={key} not found".format(key=key))/g' coreir/type.py
RUN cd pycoreir && sed -i -e 's/KeyError(f"key={key} not in params={self.params.keys()}")/KeyError("key={key} not in params={params_keys}".format(key=key, params_keys=self.params.keys()))/g' coreir/generator.py
RUN cd pycoreir && sed -i -e 's/ValueError(f"Arg(name={key}, value={value}) does not match expected type {self.params\[key\].kind}")/ValueError("Arg(name={key}, value={value}) does not match expected type {params_kind}".format(key=key, value=value, params_kind=self.params\[key\].kind))/g' coreir/generator.py
RUN cd pycoreir && sed -i -e 's/f"{self.module.name}.{self.name}"/"{module_name}.{self_name}".format(module_name=self.module.name, name=self.name)/g' coreir/wireable.py
RUN cd pycoreir && pip3 install -e .

RUN wget https://github.com/cristian-mattarei/CoSA/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv CoSA-master CoSA
RUN pip3 install pyparsing

RUN ln -s /usr/bin/python3 /usr/bin/python