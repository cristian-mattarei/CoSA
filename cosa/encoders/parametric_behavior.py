# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from typing import NamedTuple

from cosa.encoders.factory import GeneratorsFactory, ClockBehaviorsFactory
from cosa.encoders.template import ModelInformation
from cosa.representation import HTS
from cosa.utils.logger import Logger

PAR_SP = ","
MODEL_SP = ";"

class ParametricBehavior(object):

    @staticmethod
    def apply_to_problem(hts:HTS,
                         problem:NamedTuple,
                         general_config:NamedTuple,
                         model_info:ModelInformation)->HTS:

        varsdict = dict([(var.symbol_name(), var) for var in hts.vars])

        if problem.generators is not None:

            for strgenerator in problem.generators.split(MODEL_SP):
                strgenerator = strgenerator.replace(" ","")
                if strgenerator == "":
                    continue

                eqpos = strgenerator.find("=")
                parstart = strgenerator.find("(")
                if (parstart < eqpos) or (eqpos == -1):
                    Logger.error("Invalid generators")

                instance = strgenerator[:eqpos:]
                mdef = strgenerator[eqpos+1:]
                mtype = mdef.split("(")[0]
                pars = mdef[mdef.find("(")+1:-1].split(PAR_SP)
                generator = GeneratorsFactory.generator_by_name(mtype)
                pars = [varsdict[v] if v in varsdict else v for v in pars]
                ts = generator.get_sts(instance, pars)

                hts.add_ts(ts)

        if general_config.add_clock and (general_config.clock_behaviors is None):
            clk_behs = []

            for (clock, (before, after)) in model_info.abstract_clock_list:
                if (clock not in model_info.clock_list) or (clock in clk_behs):
                    continue
                clock_behavior = ClockBehaviorsFactory.get_default_abstract()
                ts = clock_behavior.get_default([clock, after])
                clk_behs.append(clock)
                hts.add_ts(ts)

            clock_list = [c for c in model_info.clock_list if c not in clk_behs]
            for clock in clock_list:
                if len(clock_list) > 1:
                    clock_behavior = ClockBehaviorsFactory.get_default_multi()
                else:
                    clock_behavior = ClockBehaviorsFactory.get_default()
                ts = clock_behavior.get_default([clock])
                clk_behs.append(clock)
                hts.add_ts(ts)

            assert len(clk_behs) == len(set(clk_behs))

        if general_config.clock_behaviors is not None:

            for strcb in general_config.clock_behaviors.split(MODEL_SP):
                strcb = strcb.replace(" ","")

                if strcb == "":
                    continue

                parstart = strcb.find("(")
                parend = strcb.find(")")

                if (parstart == -1) or (parend == -1) or (parstart > parend):
                    Logger.error("Invalid Clock Behavior definition")

                cbname = strcb[:parstart]
                pars = strcb[parstart+1:parend].split(PAR_SP)
                pars = [varsdict[v] if v in varsdict else v for v in pars]

                clock_behavior = ClockBehaviorsFactory.clockbehavior_by_name(cbname)
                ts = clock_behavior.get_sts(pars)

                hts.add_ts(ts)

        return hts
