#===============================================================================
# Modulo Parser.py
# 7 Jun 2012
# Autor: Raul Monti
#===============================================================================

"""
    Este Modulo tiene el fin de reordenar el AST resultante del metodo 
    'interpret' de la clase Interpreter del modulo Interpreter.py, para obtener 
    un manejo mas intuitivo de la informacion que contiene.
"""

from Debug import *
from Config import *


#///////////////////////////////////////////////////////////////////////////////
# 

class FallutoElem():
    def __init__(self):
        self.name = ""
        self.line = ""
#///////////////////////////////////////////////////////////////////////////////



#///////////////////////////////////////////////////////////////////////////////
#
class System():
    def __init__(self):
        self.modules = {}
        self.instances = []
        self.timeLogics = []
        self.contraints = []
        
    def printMe(self):
        for name, m in self.modules:
            m.printMe()
        for i in self.instances:
            i.printMe()
        for t in self.timeLogics:
            t.printMe()
        for c in self.contraints:
            c.printMe()

#///////////////////////////////////////////////////////////////////////////////

class ContextAct(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)

class LTLspec():
    def __init__(self):
        self.line = ""
        self.spec = ""

    def printMe(self):
            print "LTLSPEC", "at line", self.line, ":", str(self.spec)[:20], '...'
            print "\n"

            
class Var():
    def __init__(self):
        self.type = ""
        self.domain = []
        self.name = ""
        self.line = ""

class Fault():
    def __init__(self):
        self.name = ""
        self.pre = ""
        self.pos = ""
        self.line = ""

class TransFault(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)
        self.afects = []        #lista de variables que afecta

class Trans(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)
        self.pre = ""
        self.pos = ""
        self.faults = []

class Instance(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)
        self.type = ""
        self.params = []

    def printMe(self):
        print "INSTANCE", self.name, "of type", self.type, "in line", self.line

        print "\t. PARAMETERS:"
        for x in self.params:
            print "\t\t-", x
        print "\n",

class FairnessContraint(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)
        self.contraint = ""

class CompassionContraint(FallutoElem):
    def __init__(self):
        FallutoElem.__init__(self)
        self.preContraint = ""
        self.posContraint = ""
        

class Module():
    def __init__(self):
        self.line = ""
        self.name = ""
        self.contextVars = []
        self.synchroActs = []
        self.localVars = []
        self.trans = []
        self.faults = []
        self.init = []

    def printMe(self):

        print "MODULE", self.name

        print "\t. PARAMETRIC VARIABLES:"
        for x in self.contextVars:
            print "\t\t-", x.name, x.line
        print "\n",

        print "\t. PARAMETRIC ACTIONS:"
        for x in self.contextActs:
            print "\t\t-", x.name, x.line
        print "\n",

        print "\t. LOCAL VARS:"
        for x in self.localVars:
            print "\t\t-", x.name, x.type, x.domain, x.line
        print "\n",
        
        print "\t. INIT:"
        for x in self.init:
            print "\t\t-", str(x)[:20], "...  ",  x.__name__.line
        print "\n",
                
        print "\t. FAULTS:"
        for x in self.faults:
            print "\t\t-", x.name, str(x.pre)[:20], '...', str(x.pos)[:20], '...  ', x.line
        print "\n",
        
        print "\t. TRANSITIONS:"
        for x in self.trans:
            print "\t\t-", x.name, str(x.pre)[:20], '...', str(x.pos)[:20], '...  ', x.line
            print "\t\tTRANSITION FAULTS:"
            for f in x.faults:
                print "\t\t\t-", f.name
                print "\t\t\tAFECTS:"
                for x in f.afects:
                    print "\t\t\t\t.", x
        print "\n",




#===============================================================================
#EL PARSER
#===============================================================================

class Parser():

    def __init__(self):
        self.system = System()

    def retriveSystem(self):
        return self.system

    def parse(self, inputList):
        
        if DEBUGTODO__ :
            DebugTODO("FALTA PARSEAR \'LTLSPECNAME\'...")
        
        for x in inputList:
            if x.__name__ == 'MODULE':
                m = self.parseModule(x.what)
                self.system.modules[m.name] = m
            elif x.__name__ == 'INSTANCE':
                i = self.parseInstance(x.what)
                self.system.instances.append(i)
            elif x.__name__ == 'LTLSPEC':
                l = self.parseLTL(x.what[0])
                self.system.timeLogics.append(l)
            elif x.__name__ == 'FAIRNESS':
                pass
            else:
                pass

        return self.system

    def parseLTL(self, ltlspec):
        ltl = LTLspec()
        ltl.spec = ltlspec.what
        ltl.line = ltlspec.__name__.line
        return ltl

    def parseInstance(self, instance):
        inst = Instance()
        inst.name = instance[0].what
        inst.line = instance[0].__name__.line
        inst.type = instance[1].what
        for x in instance[2].what:
            inst.params.append(x)
        return inst

    def parseModule(self, module):
        m = Module()
        for x in module:
            if x.__name__ == 'IDENT':
                m.name = x.what
                m.line = x.__name__.line
            elif x.__name__ == 'CONTEXTVARS':
                for v in x.what:
                    var = Var()
                    var.name = v.what
                    var.line = v.__name__.line
                    m.contextVars.append(var)
            elif x.__name__ == 'CONTEXTACTS':
                for a in x.what:
                    act = ContextAct()
                    act.name = a.what
                    act.line = a.__name__.line
                    m.synchroActs.append(act)
            elif x.__name__ == 'MODULEBODY':
                for e in x.what:
                    if e.__name__ == 'VAR':
                        m.localVars += self.parseVars(e.what)
                    elif e.__name__ == 'FAULT':
                        m.faults += self.parseFaults(e.what)
                    elif e.__name__ == 'INIT':
                        m.init += e.what[0].what
                    elif e.__name__ == 'TRANS':
                        m.trans = self.parseTrans(e.what)
                    else:
                        pass
            else:
                pass

        return m

    def parseTrans(self, trans):
        trlist = []
        for t in trans:
            tr = Trans()
            tr.line = t.__name__.line
            for x in t.what:
                if x.__name__ == 'IDENT':
                    tr.name = x.what
                elif x.__name__ == 'PROPFORM':
                    tr.pre = x.what
                elif x.__name__ == 'NEXTPROPFORM':
                    tr.pos = x.what
                elif x.__name__ == 'PFAULTDECL':
                    for f in x.what:
                        flt = TransFault()
                        flt.name = f.__name__
                        for z in f.what:
                            flt.afects.append(z.what)
                        tr.faults.append(flt)
                else:
                    raise BaseException
            trlist.append(tr)
        return trlist


    def parseVars(self, var):
        vl = []
        for v in var:
            var = Var()
            v = v.what
            var.line = v[0].__name__.line
            var.name = v[0].what
            var.type = v[1].__name__
            var.domain = [x.what for x in v[1].what]
            vl.append(var)
        return vl



    def parseFaults(self, faults):
        fl = []
        for f in faults:
            flt = Fault()
            flt.name = f.what[0].what
            flt.line = f.__name__.line
            try:
                flt.pre = f.what[1].what
                flt.pos = f.what[2].what
            except:
                pass
            fl.append(flt)
        return fl

#===============================================================================


