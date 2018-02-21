# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Symbol, And, TRUE

NEXT = "_N"
AT = "_AT"
SEP = "$"

class HTS(object):

    tss = None
    sub = None
    name = None
    
    def __init__(self, name):
        self.tss = []
        self.sub = []
        self.vars = set([])
        self.name = name

    def add_ts(self, ts):
        self.ts.append(ts)

    def add_sub(self, sub):
        self.sub.append(sub)

    def add_var(self, var):
        self.vars.add(var)
        
    def add_ts(self, ts):
        self.tss.append(ts)
        self.vars = set(self.vars.union(ts.vars))

    def remove_invars(self):
        for ts in self.tss:
            ts.remove_invar()

    def single_init(self):
        init = TRUE()
        for ts in self.tss:
            if ts.init is not None:
                init = And(init, ts.init)

        return init

    def single_trans(self):
        trans = TRUE()
        for ts in self.tss:
            if ts.trans is not None:
                trans = And(trans, ts.trans)

        return trans

    def single_invar(self):
        invar = TRUE()
        for ts in self.tss:
            if ts.invar is not None:
                invar = And(invar, ts.invar)

        return invar
    
class TS(object):

    vars = None
    init = None
    trans = None
    invar = None
    
    comment = None
    
    def __init__(self, vars, init, trans, invar):
        self.vars = vars
        self.init = init
        self.trans = trans
        self.invar = invar

        self.comment = None

    def remove_invar(self):
        if self.invar is not None:
            self.trans = And([self.trans, self.invar, TS.to_next(self.invar)])
            self.init = And(self.init, self.invar)

        self.invar = None

    @staticmethod
    def get_prime(v):
        return Symbol(("%s"+NEXT) % v.symbol_name(), v.symbol_type())

    @staticmethod
    def is_prime(v):
        return v.symbol_name()[-len(NEXT):] == NEXT

    @staticmethod
    def get_timed(v, t):
        return Symbol("%s%s%s" % (v.symbol_name(), AT, str(t)), v.symbol_type())
    
    @staticmethod
    def to_next(formula):
        varmap = dict([(v,TS.get_prime(v)) for v in formula.get_free_variables()])
        return formula.substitute(varmap)

    
