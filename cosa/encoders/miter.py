# Copyright 2018 Cristian Mattarei and Makai Mann
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import TRUE, FALSE, BOOL, And, EqualsOrIff, Iff, Symbol, Implies

from cosa.representation import HTS, TS
from cosa.encoders.coreir import SEP
from cosa.encoders.formulae import StringParser
from cosa.utils.logger import Logger
from cosa.utils.formula_mngm import substitute, get_free_variables


S1 = "sys1"+SEP
S2 = "sys2"+SEP
EQS = "eq_S1_S2"

class Miter(object):

    @staticmethod
    def combine_systems(hts, hts2, k, symbolic_init, eqprop=None, inc=True, non_deterministic=False):
        htseq = HTS("eq")

        hts1_varnames = [v.symbol_name() for v in hts.vars]
        hts2_varnames = [v.symbol_name() for v in hts2.vars]
        
        map1 = dict([(v, TS.get_prefix_name(v, S1)) for v in hts1_varnames]+\
                    [(TS.get_prime_name(v), TS.get_prefix_name(TS.get_prime_name(v), S1)) for v in hts1_varnames])
        map2 = dict([(v, TS.get_prefix_name(v, S2)) for v in hts2_varnames]+\
                    [(TS.get_prime_name(v), TS.get_prefix_name(TS.get_prime_name(v), S2)) for v in hts2_varnames])

        ts1_init = TRUE()
        ts2_init = TRUE()

        if not symbolic_init:
            ts1_init = substitute(hts.single_init(), map1)
            ts2_init = substitute(hts2.single_init(), map2)

        ts1 = TS()
        ts1.vars = set([TS.get_prefix(v, S1) for v in hts.vars])
        ts1.set_behavior(ts1_init,\
                         substitute(hts.single_trans(), map1),\
                         substitute(hts.single_invar(), map1))
        ts1.state_vars = set([TS.get_prefix(v, S1) for v in hts.state_vars])

        ts2 = TS()
        ts2.vars = set([TS.get_prefix(v, S2) for v in hts2.vars])
        ts2.set_behavior(ts2_init,\
                         substitute(hts2.single_trans(), map2),\
                         substitute(hts2.single_invar(), map2))
        ts2.state_vars = set([TS.get_prefix(v, S2) for v in hts2.state_vars])

        htseq.add_ts(ts1)
        htseq.add_ts(ts2)

        assumptions = []
        lemmas = []

        def sets_intersect(set1, set2):
            for el in set1:
                if not el in set2:
                    return False
            return True
        
        if hts.assumptions is not None:
            for assumption in hts.assumptions:
                assumptions.append(assumption)

        if hts.lemmas is not None:
            for lemma in hts.lemmas:
                lemmas.append(lemma)

        if hts2.assumptions is not None:
            for assumption in hts2.assumptions:
                assumptions.append(assumption)

        if hts2.lemmas is not None:
            for lemma in hts2.lemmas:
                lemmas.append(lemma)
                
        for assumption in assumptions:
            fv_assumption = get_free_variables(assumption)
            c_assumption = TRUE()
            
            if sets_intersect(fv_assumption, hts.vars):
                c_assumption = And(c_assumption, substitute(assumption, map1))
            if sets_intersect(fv_assumption, hts2.vars):
                c_assumption = And(c_assumption, substitute(assumption, map2))

            if c_assumption != TRUE():
                htseq.add_assumption(c_assumption)

        for lemma in lemmas:
            fv_lemma = get_free_variables(lemma)
            c_lemma = TRUE()
            
            if sets_intersect(fv_lemma, hts.vars):
                c_lemma = And(c_lemma, substitute(lemma, map1))
            if sets_intersect(fv_lemma, hts2.vars):
                c_lemma = And(c_lemma, substitute(lemma, map2))

            if c_lemma != TRUE():
                htseq.add_lemma(c_lemma)
                
        miter_out = Symbol(EQS, BOOL)

        inputs = hts.input_vars.intersection(hts2.input_vars)
        outputs = hts.output_vars.intersection(hts2.output_vars)

        htseq.input_vars = set([TS.get_prefix(v, S1) for v in hts.input_vars]).union(set([TS.get_prefix(v, S2) for v in hts2.input_vars]))
        htseq.output_vars = set([TS.get_prefix(v, S1) for v in hts.output_vars]).union(set([TS.get_prefix(v, S2) for v in hts2.output_vars]))

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

        tsmo = TS()
        tsmo.vars = set([miter_out])
        tsmo.invar = invar
        htseq.add_ts(tsmo)

        return (htseq, miter_out)
