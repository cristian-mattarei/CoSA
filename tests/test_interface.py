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

from CoSA import Config, run_verification
from pysmt.shortcuts import reset_env

abspath = os.path.abspath(__file__)
path = ("/".join(abspath.split("/")[:-1]))
testmodels = [(d[0], d[0]+"/"+[f for f in d[2] if ".json" in f][0]) for d in os.walk(path) if d[0] != path and "__" not in d[0]]

EXPECTED = "/expected.smv"
GENERATED = "/test.smv"

def files_eq(file1, file2):
    with open(file1, "r") as f1:
        strf1 = f1.read()

    with open(file2, "r") as f2:
        strf2 = f2.read()

    return strf1 == strf2

def runtest(test):
    reset_env()
    (path, example) = test
    config = Config()
    status = True
    
    config.safety = True
    config.verbosity = 3
    config.solver_name = "msat"
    config.prove = True
    config.strfiles = example
    config.translate = path+GENERATED
    config.printer = "SMV"
    config.deterministic = True

    run_verification(config)

    status = files_eq(path+EXPECTED, path+GENERATED)
    assert status
    return status
    
def test_problem():
    for test in testmodels:
        yield runtest, test

if __name__ == "__main__":
    for test in testmodels:
        runtest(test)
