# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, Symbol, And, Implies, TRUE, BV
from pysmt.typing import BOOL, BVType

from cosa.representation import HTS, TS
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables
from cosa.printers.template import HIDDEN_VAR

NOMIN = HIDDEN_VAR+"%s_REF_"
#NOMIN = "%s_REF_"
FAIL = "|FAILURE|"
FAULT = "%s"+FAIL

class ModelExtensionStrategy(object):
    NONE = None
    ALL = "ALL"

class ModelExtension(object):

    @staticmethod
    def get_strategies():
        strategies = []
        strategies.append((ModelExtensionStrategy.NONE, "Not applied"))
        strategies.append((ModelExtensionStrategy.ALL,  "Extends all state variables with a non-deterministic behavior"))

        return strategies
    
    @staticmethod
    def extend(hts, strategy):
        if strategy == ModelExtensionStrategy.NONE:
            return hts

        if strategy not in [x[0] for x in ModelExtension.get_strategies()]:
            Logger.error("Invalid model extension mode \"%s\""%(strategy))
        
        is_flatten = hts.is_flatten
        if is_flatten:
            hts.reset_flatten()

        ModelExtension.extend_all(hts)

        if is_flatten:
            hts.flatten()
            
        return hts
    
    @staticmethod
    def extend_all(hts):
        tss = []
        for ts in hts.tss:
            ts, vars = ModelExtension.extend_ts(ts)
            tss.append(ts)
            for v in vars:
                hts.add_var(v)
        hts.tss = set(tss)

        for sub in hts.subs:
            ModelExtension.extend_all(sub[2])

    @staticmethod
    def get_parameters(hts):
        return [v for v in hts.vars if FAIL in v.symbol_name()]
            
    @staticmethod
    def extend_ts(ts):

        affect_init = False
        
        if ts.ftrans is None:
            return (ts, [])
        
        new_ftrans = {}
        
        for (assign, cond_assign_list) in ts.ftrans.items():
            fv = get_free_variables(assign)
            assert len(fv) == 1
            var = fv.pop()
            is_next = TS.has_next(var)

            refvar = TS.get_ref_var(var)
            nomvar = Symbol(NOMIN%refvar.symbol_name(), var.symbol_type())
            fvar = Symbol(FAULT%refvar.symbol_name(), BOOL)

            ts.add_var(nomvar)
            ts.add_var(fvar)
            
            repldic = dict([(refvar.symbol_name(), nomvar.symbol_name()), \
                            (TS.get_prime(refvar).symbol_name(), TS.get_prime(nomvar).symbol_name())])

            new_ftrans[substitute(assign, repldic)] = [(substitute(c[0], repldic), substitute(c[1], repldic)) for c in cond_assign_list]

            #new_ftrans[refvar] = [(Not(fvar), nomvar), (fvar, BV(1, nomvar.symbol_type().width))]
            new_ftrans[refvar] = [(Not(fvar), nomvar)]

            ts.trans = And(ts.trans, Implies(fvar, TS.get_prime(fvar)))

            if affect_init:
                ts.init = substitute(ts.init, repldic)
            else:
                ts.init = And(ts.init, Not(fvar))

        ts.ftrans = new_ftrans

        return (ts, [fvar, nomvar])
                


