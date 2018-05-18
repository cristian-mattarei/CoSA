# Copyright 2018 Cristian Mattarei and Makai Mann
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.transition_systems import HTS, TS
from cosa.encoders.coreir import SEP
from cosa.utils.logger import Logger
from cosa.encoders.formulae import StringParser
from pysmt.shortcuts import TRUE, FALSE, BOOL, And, EqualsOrIff, Iff, Symbol, Implies

S1 = "sys1"+SEP
S2 = "sys2"+SEP
EQS = "eq_S1_S2"

class Miter(object):

    @staticmethod
    def combine_systems(hts, hts2, k, symbolic_init, eqprop=None, inc=True, non_deterministic=False):
        htseq = HTS("eq")

        map1 = dict([(v, TS.get_prefix(v, S1)) for v in hts.vars]+[(TS.get_prime(v), TS.get_prefix(TS.get_prime(v), S1)) for v in hts.vars])
        map2 = dict([(v, TS.get_prefix(v, S2)) for v in hts2.vars]+[(TS.get_prime(v), TS.get_prefix(TS.get_prime(v), S2)) for v in hts2.vars])

        ts1_init = TRUE()
        ts2_init = TRUE()

        if not symbolic_init:
            ts1_init = hts.single_init().substitute(map1)
            ts2_init = hts2.single_init().substitute(map2)

        ts1 = TS(set([TS.get_prefix(v, S1) for v in hts.vars]),\
                 ts1_init,\
                 hts.single_trans().substitute(map1),\
                 hts.single_invar().substitute(map1))
        ts1.state_vars = set([TS.get_prefix(v, S1) for v in hts.state_vars])

        ts2 = TS(set([TS.get_prefix(v, S2) for v in hts2.vars]),\
                 ts2_init,\
                 hts2.single_trans().substitute(map2),\
                 hts2.single_invar().substitute(map2))
        ts2.state_vars = set([TS.get_prefix(v, S2) for v in hts2.state_vars])

        htseq.add_ts(ts1)
        htseq.add_ts(ts2)

        miter_out = Symbol(EQS, BOOL)

        inputs = hts.inputs.intersection(hts2.inputs)
        outputs = hts.outputs.intersection(hts2.outputs)

        htseq.inputs = set([TS.get_prefix(v, S1) for v in hts.inputs]).union(set([TS.get_prefix(v, S2) for v in hts2.inputs]))
        htseq.outputs = set([TS.get_prefix(v, S1) for v in hts.outputs]).union(set([TS.get_prefix(v, S2) for v in hts2.outputs]))

        if symbolic_init or (not non_deterministic):
            states = hts.state_vars.intersection(hts2.state_vars)
        else:
            states = []

        eqinputs = TRUE()
        eqoutputs = TRUE()
        eqstates = TRUE()

        for inp in inputs:
            eqinputs = And(eqinputs, EqualsOrIff(TS.get_prefix(inp, S1), TS.get_prefix(inp, S2)))

        for out in outputs:
            eqoutputs = And(eqoutputs, EqualsOrIff(TS.get_prefix(out, S1), TS.get_prefix(out, S2)))

        for svar in states:
            eqstates = And(eqstates, EqualsOrIff(TS.get_prefix(svar, S1), TS.get_prefix(svar, S2)))

        if eqprop is None:
            if symbolic_init or (not non_deterministic):
                invar = And(eqinputs, Iff(miter_out, Implies(eqstates, eqoutputs)))
            else:
                invar = And(eqinputs, Iff(miter_out, eqoutputs))

            Logger.log('Inferring equivalence property: {}'.format(invar), 2)
        else:
            sparser = StringParser()
            eqprop = sparser.parse_formulae(eqprop)
            if len(eqprop) > 1:
                Logger.error("Expecting a single equivalence property")
            eqprop = eqprop[0][1]
            invar = Iff(miter_out, eqprop)
            Logger.log('Using provided equivalence property: {}'.format(invar), 2)

        htseq.add_ts(TS(set([miter_out]), TRUE(), TRUE(), invar))

        return (htseq, miter_out)
