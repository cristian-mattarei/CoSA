# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import sys
import time
import inspect

ERROR = "ERROR: "

class Logger(object):
    verbosity = 0
    linenum_verbosity = 5
    id_timer = 0
    timers = []
    time = False
    single_warnings = True
    prev_warnings = None
    error_raise_exept = True
    newline = True

    _last_inline = None
    
    @staticmethod        
    def msg(msg, level, condition=True, max_level=10):
        if Logger.verbosity > 1:
            Logger.log(msg, level, condition, max_level)
        else:
            if (Logger.verbosity > level) and (Logger.verbosity <= max_level+1) and (condition):
                sys.stdout.write(msg)
                sys.stdout.flush()
                Logger.newline = "\n" in msg

    @staticmethod        
    def inline(msg, level, condition=True, max_level=10):
        if (Logger.verbosity > level) and (Logger.verbosity <= max_level+1) and (condition):
            Logger.clear_inline(0)
            lmsg = len(msg)
            Logger._last_inline = lmsg
            sys.stdout.write(msg)
            sys.stdout.write('\b'*lmsg)
            sys.stdout.flush()
            Logger.newline = "\n" in msg

    @staticmethod        
    def clear_inline(level, condition=True, max_level=10):
        if Logger._last_inline is not None:
            if (Logger.verbosity > level) and (Logger.verbosity <= max_level+1) and (condition):
                sys.stdout.write(' '*Logger._last_inline)
                sys.stdout.write('\b'*Logger._last_inline)
                sys.stdout.flush()
                Logger._last_inline = None
                Logger.newline = True

    @staticmethod        
    def line_number():
        previous_frame = inspect.currentframe().f_back.f_back
        (filename, line_number, _, _, _) = inspect.getframeinfo(previous_frame)
        return (filename, line_number)
                
    @staticmethod        
    def log(msg, level, condition=True, max_level=10):
        if (Logger.verbosity > level) and (Logger.verbosity <= max_level+1) and (condition):
            if Logger.verbosity >= Logger.linenum_verbosity:
                filename, line_number = Logger.line_number()
                msg = "\"%s\"\nfrom %s:%d"%(msg, filename, line_number)
                
            sys.stdout.write(msg+"\n")
            sys.stdout.flush()
            Logger.newline = True

    @staticmethod        
    def error(msg, raise_exception=True):
        if not Logger.newline:
            sys.stderr.write("\n")
            Logger.newline = True
        if not (Logger.error_raise_exept and raise_exception):
            sys.stderr.write("%s%s\n"%(ERROR, msg))
            sys.stderr.flush()
            sys.exit(1)
            
        raise RuntimeError(msg)

    @staticmethod        
    def warning(msg):
        if Logger.single_warnings:
            if Logger.prev_warnings is None:
                Logger.prev_warnings = []

            if msg not in Logger.prev_warnings:
                if not Logger.newline:
                    sys.stderr.write("\n")
                    Logger.newline = True
                
                sys.stderr.write("WARNING: "+msg+"\n")
                sys.stderr.flush()
                Logger.prev_warnings.append(msg)
        else:
            if not Logger.newline:
                sys.stderr.write("\n")
                Logger.newline = True
            sys.stderr.write("WARNING: "+msg+"\n")
            sys.stderr.flush()
        
    @staticmethod        
    def level(level):
        return Logger.verbosity > level

    @staticmethod        
    def start_timer(name, print_time=True):
        if not Logger.time:
            return None
        if print_time:
            sys.stdout.write("Timer \"%s\": start\n"%(name))
            sys.stdout.flush()
        Logger.timers.append((time.time(), name))
        Logger.id_timer += 1
        return Logger.id_timer-1

    @staticmethod        
    def get_timer(id_timer, print_time=True):
        if not Logger.time:
            return None
        diff = time.time() - Logger.timers[id_timer][0]
        if print_time:
            sys.stdout.write("Timer \"%s\": %.2f sec\n"%(Logger.timers[id_timer][1], diff))
            sys.stdout.flush()
        return diff
