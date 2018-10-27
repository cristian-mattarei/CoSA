# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os

from cosa.shell import Config, run_verification
from pysmt.shortcuts import reset_env

COSADIR = ".CoSA"
EXPECTED = "/expected.smv"
GENERATED = "/test.smv"

abspath = os.path.abspath(__file__)
path = ("/".join(abspath.split("/")[:-1]))
testdirs = [d[0] for d in os.walk(path) if d[0] != path and "__" not in d[0] and COSADIR not in d[0]]

def files_eq(file1, file2):
    with open(file1, "r") as f1:
        strf1 = f1.read()

    with open(file2, "r") as f2:
        strf2 = f2.read()

    return strf1 == strf2

def run_translation(path):
    reset_env()

    config = Config()
    status = True
    
    config.verbosity = 3
    config.solver_name = "msat"
    config.prove = True
    config.translate = path+GENERATED
    config.printer = "SMV"
    config.deterministic = True

    if "-boolean" in path:
        config.boolean = True
    
    if os.path.isfile("%s/assumptions.txt"%path):
        config.assumptions = "%s/assumptions.txt"%path

    if os.path.isfile("%s/properties.txt"%path):
        config.properties = "%s/properties.txt"%path

    if os.path.isfile("%s/lemmas.txt"%path):
        config.lemmas = "%s/lemmas.txt"%path

    models = list([x for x in list(os.walk(path)) if COSADIR not in x[0]])[-1][-1]
        
    j_files = ["%s/%s"%(path,f) for f in models if f.split(".")[1] == "json"]
    s_files = ["%s/%s"%(path,f) for f in models if f.split(".")[1] in ["sts","ets"]]
    v_files = ["%s/%s[%s]"%(path,f, f.split(".")[0]) for f in models if f.split(".")[1] in ["v"]]
    
    config.strfiles = ",".join(j_files+s_files+v_files)
        
    parsing_defs = [config.properties, config.lemmas, config.assumptions]
    for i in range(len(parsing_defs)):
        if parsing_defs[i] is not None:
            if os.path.isfile(parsing_defs[i]):
                with open(parsing_defs[i]) as f:
                    parsing_defs[i] = [p.strip() for p in f.read().strip().split("\n")][0]
            else:
                parsing_defs[i] = [p.strip() for p in parsing_defs[i].split(",")][0]

    [config.properties, config.lemmas, config.assumptions] = parsing_defs

    run_verification(config)

    # status = files_eq(path+EXPECTED, path+GENERATED)
    # assert status
    return status
    
def test_translation():
    for test in testdirs:
        yield run_translation, test

if __name__ == "__main__":
    for test in testdirs:
        run_translation(test)
