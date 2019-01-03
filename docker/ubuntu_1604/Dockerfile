FROM ubuntu:16.04
WORKDIR /home/CoSA

RUN apt-get update --fix-missing
RUN apt-get install -y python3-pip libpcre* wget unzip build-essential python3 automake libgmp-dev curl nano python3-dev libboost-dev default-jdk libclang-dev llvm llvm-dev lbzip2 libncurses5-dev git libtool iverilog

RUN wget https://github.com/pysmt/pysmt/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv pysmt-master pysmt
RUN cd pysmt && pip3 install -e . && pysmt-install --msat --confirm-agreement --install-path solvers --bindings-path bindings
ENV PYTHONPATH="/home/CoSA/pysmt/bindings:${PYTHONPATH}"
ENV LD_LIBRARY_PATH="/home/CoSA/pysmt/bindings:${LD_LIBRARY_PATH}"

RUN wget https://github.com/rdaly525/coreir/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv coreir-master coreir
RUN cd coreir && make -j4 && make install

RUN wget https://github.com/leonardt/bit_vector/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv bit_vector-master bit_vector
RUN cd bit_vector && sed -i -e 's/f"BitVector({self._value}, {self.num_bits})"/"BitVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
RUN cd bit_vector && sed -i -e 's/f"UIntVector({self._value}, {self.num_bits})"/"UIntVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
RUN cd bit_vector && sed -i -e 's/f"SIntVector({self._value}, {self.num_bits})"/"SIntVector({self_value}, {selfnum_bits})".format(self_value=self._value, selfnum_bits=self.num_bits)/g' bit_vector/bit_vector.py
RUN cd bit_vector && pip3 install -e .

RUN wget https://github.com/leonardt/pycoreir/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv pycoreir-master pycoreir
RUN cd pycoreir && sed -i -e 's/KeyError(f"key={key} not found")/Error("key={key} not found".format(key=key))/g' coreir/type.py
RUN cd pycoreir && sed -i -e 's/KeyError(f"key={key} not in params={self.params.keys()}")/KeyError("key={key} not in params={params_keys}".format(key=key, params_keys=self.params.keys()))/g' coreir/generator.py
RUN cd pycoreir && sed -i -e 's/ValueError(f"Arg(name={key}, value={value}) does not match expected type {self.params\[key\].kind}")/ValueError("Arg(name={key}, value={value}) does not match expected type {params_kind}".format(key=key, value=value, params_kind=self.params\[key\].kind))/g' coreir/generator.py
RUN cd pycoreir && sed -i -e 's/f"{self.module.name}.{self.name}"/"{module_name}.{self_name}".format(module_name=self.module.name, name=self.name)/g' coreir/wireable.py
RUN cd pycoreir && sed -i -e 's/f"Cannot select path {field}"/"Cannot select path {field}".format(field=field)/g' coreir/module.py
RUN cd pycoreir && pip3 install -e .

RUN wget https://github.com/cristian-mattarei/CoSA/archive/master.zip
RUN unzip master.zip
RUN rm master.zip
RUN mv CoSA-master CoSA
RUN cd CoSA && pip3 install -e .
