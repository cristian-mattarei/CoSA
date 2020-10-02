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

from cosa.shell import run_problems
from cosa.options import cosa_option_manager
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

    status = True

    if "-boolean" in path:
        boolean = True
    else:
        boolean = False

    models = list([x for x in list(os.walk(path)) if COSADIR not in x[0]])[-1][-1]

    j_files = ["%s/%s"%(path,f) for f in models if f.split(".")[1] == "json"]
    s_files = ["%s/%s"%(path,f) for f in models if f.split(".")[1] in ["sts","ets"]]
    v_files = ["%s/%s[%s]"%(path,f, f.split(".")[0]) for f in models if f.split(".")[1] in ["v"]]
    btor2_files = ["%s/%s[%s]"%(path,f, f.split(".")[0]) for f in models if f.split(".")[1] in ["btor", 'btor2']]

    if os.path.isfile("%s/assumptions.txt"%path):
        assumptions = "%s/assumptions.txt"%path
    else:
        assumptions = None

    if os.path.isfile("%s/properties.txt"%path):
        properties = "%s/properties.txt"%path
    else:
        properties = None

    if os.path.isfile("%s/lemmas.txt"%path):
        lemmas = "%s/lemmas.txt"%path
    else:
        lemmas = None

    problems_manager = cosa_option_manager.get_default_problem_manager(
        verbosity=3,
        boolean=boolean,
        translate=path+GENERATED,
        printer='SMV',
        model_files=",".join(j_files+s_files+v_files+btor2_files))

    problems_manager.add_problem(solver_name='msat',
                                 verification='safety' if properties is not None else "simulation",
                                 prove=True if properties is not None else False,
                                 assumptions=assumptions,
                                 properties=properties,
                                 lemmas=lemmas
                                 )
    run_problems(problems_manager)

    # status = files_eq(path+EXPECTED, path+GENERATED)
    # assert status
    return status

def test_translation():
    for test in testdirs:
        yield run_translation, test

if __name__ == "__main__":
    for test in testdirs:
        run_translation(test)
