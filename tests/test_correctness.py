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

from CoSA import Config, run

abspath = os.path.abspath(__file__)
path = ("/".join(abspath.split("/")[:-1]))
testdirs = [d[0] for d in os.walk(path) if d[0] != path and "__" not in d[0]]

def runtest(example):
    config = Config()

    config.strfile = "%s/model.json"%example
    config.safety = True
    config.verbosity = 1
    config.solver_name = "z3"
    with open("%s/properties.txt"%example, "r") as f:
        config.properties = [a.strip() for a in f.read().strip().split("\n")]
    
    list_status = list(set(run(config)))

    return len(list_status) == 1 and list_status[0] == True
    
def test_safety():
    for test in testdirs:
        yield runtest, test

if __name__ == "__main__":
    for test in testdirs:
        runtest(test)
