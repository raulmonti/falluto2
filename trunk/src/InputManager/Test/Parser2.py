# sabado 23 de Junio 2012
# Raul Monti

import sys, os
sys.path.append(os.path.abspath('../../'))

from Debug import *
from Config import *
from InputManager.pyPEG.pyPEG import Symbol

if DEBUG__:
    DebugGREEN("Revisar si es buena idea lo del pseudo ENUM de la clase Types")



class Types():
    SYSTEM = 0
    MODULE = 1
    inverse = { 0:'SYSTEM', 1:'MODULE'}


class FallutoBaseElem():
    def __init__(self):
        self.name = ""
        self.line = ""
        self.type = ""
    
    def printMe(self):
        print "Parser2.py", Types.inverse[self.type], \
        "default printMe():", self.name

    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
        Types.inverse[self.type]


"""
Una clase por casi cada "cosa" interpretada:
"""

class System(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.SYSTEM
        self.modules = {}
        self.instances = {}
        self.ltlspecs = []
        self.contraints = []

    def printMe(self):
        print "SYSTEM STARTS AT", self.line
        print "<MODULES>"
        for m in self.modules.itervalues():
            m.printMe()
    
    def parse(self, AST):
        self.name = "NO NAME FOR SYSTEMS YET :S"
        if AST != []:
            self.line = AST[0].__name__.line
        for elem in AST:
            if elem.__name__ == "MODULE":
                m = Module()
                m.parse(elem)
                self.modules[m.name] = m


class Module(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.MODULE
        self.contextVars = []
        self.synchroActs = []
        self.localVars = []
        self.init = []
        self.faults = []
        self.trans = []

    def parse(self, AST):
        if DEBUG__:
            DebugYELLOW("Parsing Module: " + str(AST) + " at " + AST.__name__.line)
        assert AST != []
        self.line = AST.__name__.line
        AST = AST.what # AST = [ name, contextvars, synchroacts, body]
        self.name = AST[0].what
        
        for v in AST[1].what:
            self.contextVars.append(v)
        for a in AST[2].what:
            self.synchroActs.append(a)

    def printMe(self):
        print "Module", self.name, "at", self.line
        print "< ContextVars >"
        for c in self.contextVars:
            print c,
        print "\n< SynchroActs >"
        for a in self.synchroActs:
            print a,
        print "\n",



from GrammarRules2 import SYSTEM, COMMENT
from InputManager.pyPEG.pyPEG import parse
import fileinput
if __name__ == '__main__':

    files = fileinput.input()
    ast = parse(SYSTEM(), files, True, COMMENT)
    s = System()
    s.parse(ast)
    s.printMe()


