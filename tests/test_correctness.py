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

from CoSA import Config, run_verification, run_problems
from pysmt.shortcuts import Symbol, reset_env

abspath = os.path.abspath(__file__)
path = ("/".join(abspath.split("/")[:-1]))
testdirs = [d[0] for d in os.walk(path) if d[0] != path and "__" not in d[0]]

def runtest(example):
    reset_env()
    
    config = Config()

    config.safety = True
    config.verbosity = 3
    config.solver_name = "msat"
    config.prove = True
    config.vcd = True
    
    list_status = run_problems("%s/problem.txt"%example, config)

    with open("%s/expected_results.txt"%example, "r") as f:
        expected_results = f.read().strip().replace(" ","").split(",")

    assert list_status == expected_results
    return list_status == expected_results
    
def test_problem():
    for test in testdirs:
        yield runtest, test

if __name__ == "__main__":
    for test in testdirs:
        runtest(test)
