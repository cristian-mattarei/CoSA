# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import inspect

VPARSER = True

try:
    from pyverilog.vparser.ast import Node, ModuleDef
except:
    VPARSER = False

from cosa.utils.generic import class_name
from cosa.utils.logger import Logger

class VerilogWalker(object):
    methods = None
    modulesdic = None

    preserve_main_name = False

    parsed = None
    
    def __init__(self):
        pass

    def reset_structures(self, modulename):
        Logger.error("Unimplemented")
    
    def __init_methods(self):
        if self.methods is None:
            self.methods = [x[0] for x in inspect.getmembers(self, predicate=inspect.ismethod)]    
        
    def analyze_element(self, modulename, el, args):
        if not VPARSER:
            Logger.error("Pyverilog is not available")
        Logger.log("(%d) Processing Node: %s ---> %s"%(el.lineno, \
                                                       class_name(el), \
                                                       None if el.children() is None else [class_name(c) for c in el.children()]), 3)
        Logger.log("(%d) Args: %s"%(el.lineno, str(args)), 4)
        self.__init_methods()
        
        classname = class_name(el)
        if classname in self.methods:
            local_handler = getattr(self, classname)
            return local_handler(modulename, el, args)

        Logger.error("Unmanaged Node type \"%s\", line %d"%(classname, el.lineno))
        return el

    def walk(self, ast, modulename):
        description = ast.children()[0]
        modules = description.children()
        self.reset_structures(modulename)
        for m in modules:
            if type(m) == ModuleDef:
                self.modulesdic[m.name] = m
        if modulename not in self.modulesdic:
            Logger.error("Undefined module \"%s\""%(modulename))
        return self.walk_module(self.modulesdic[modulename], \
                                modulename if self.preserve_main_name else "")
    
    def walk_module(self, ast, modulename):
        if VerilogWalker.parsed is None:
            VerilogWalker.parsed = {}
            
        Logger.log("(%d) Parsing module \"%s\""%(ast.lineno, ast.name), 2)

        key = (id(ast), modulename)
        if key in VerilogWalker.parsed:
            assert VerilogWalker.parsed[key] is not None
            to_visit = [x for x in VerilogWalker.parsed[key]]
        else:
            to_visit = [ast]
            visited = []
            args = None

            i = 0
            while i < len(to_visit):
                el = to_visit[i]
                if id(el) in visited:
                    i += 1
                    continue
                visited.append(id(el))
                if isinstance(el, Node) and len(list(el.children())) > 0:
                    Logger.log("(%d) Collecting Node: %s ---> %s"%(el.lineno, \
                                                                   class_name(el), \
                                                                   None if el.children() is None else [class_name(c) for c in el.children()]), 3)
                    child = list(el.children())
                    to_visit = to_visit[:i] + child + to_visit[i:]
                    
            VerilogWalker.parsed[key] = [x for x in to_visit]
                    
        prevels = []
        processed = []
        memoization = {}
        while len(to_visit) > 0:
            el = to_visit.pop(0)
            elc = list(el.children())
            children = None
            if (len(elc) > 0) and ([type(p) for p in prevels[-len(elc):]] == [type(p) for p in elc]):
                children = processed[-len(elc):]
                prevels = prevels[:len(prevels)-len(elc)]
                processed = processed[:len(processed)-len(elc)]

            if id(el) in memoization:
                nel = memoization[id(el)]
            else:
                nel = self.analyze_element(modulename, el, children)
                memoization[id(el)] = nel
            prevels.append(el)
            processed.append(nel)

        Logger.log("(%d) Done parsing module \"%s\""%(ast.lineno, ast.name), 2)

        return processed[0]
    
class IdentityVerilogWalker(VerilogWalker):

    def Paramlist(self, modulename, el, args):
        return el

    def Port(self, modulename, el, args):
        return el

    def Portlist(self, modulename, el, args):
        return el

    def Wire(self, modulename, el, args):
        return el

    def Reg(self, modulename, el, args):
        return el
    
    def Decl(self, modulename, el, args):
        return el

    def Sens(self, modulename, el, args):
        return el
        
    def Lvalue(self, modulename, el, args):
        return el

    def Rvalue(self, modulename, el, args):
        return el

    def NonblockingSubstitution(self, modulename, el, args):
        return el
    
    def SensList(self, modulename, el, args):
        return el
    
    def IntConst(self, modulename, el, args):
        return el

    def Identifier(self, modulename, el, args):
        return el
    
    def Width(self, modulename, el, args):
        return el

    def Input(self, modulename, el, args):
        return el
    
    def Output(self, modulename, el, args):
        return el

    def Block(self, modulename, el, args):
        return el

    def IfStatement(self, modulename, el, args):
        return el

    def Always(self, modulename, el, args):
        return el

    def ModuleDef(self, modulename, el, args):
        return el

    def Description(self, modulename, el, args):
        return el

    def Source(self, modulename, el, args):
        return el
