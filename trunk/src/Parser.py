# sabado 23 de Junio 2012
# Raul Monti


from Debug import *
from Config import *
from InputManager.pyPEG.pyPEG import *
from Exceptions.Exceptions import *
import InputManager.pyPEG.pyPEG as pyPEG
from GrammarRules import SYSTEM, COMMENT



debugSOLVED("Cambiar precondiciones vacias por TRUE en el parser."        \
            + "Solution: kakasa, directly changed precondition value for" \
            + " [True] :s Better solution will be to make a PyAST and "   \
            + "call for the propform parse method in the preconditions."  )

debugTODO("Revisar si es buena idea lo del pseudo ENUM de la clase Types" \
            + "Queda bastante feo, usar el campo type para algo mejor.")
debugTODO("pyPEG tiene problemas con la primera y ultima lineas de el " + \
         "archivo de entrada :S, es como que no las detecta en .line")

debugTODO("Module contextvars and synchroacts quizas deberian poseer " + \
          "clase propia y no ser parseadas en Module.")
debugTODO("Cambiar los printMe() por __string__ o __unicode__.")
debugTODO("Chequeo exahustivo usando input bien grande y abarcativo.")
debugTODO("Clase Types y todo lo que hago con ella esta al reverendo pedo.")

debugTODO("Comprobar redaccion y ortografia con algun traductor :s")



################################################################################
################################################################################
################################################################################
"""
    Module main function
"""
class Parser():

    def __init__(self):
        pass


    def parse( self, inputFile):
        
        ast = pyPEG.parse(SYSTEM, inputFile, True, COMMENT, lineCount = True)
        parsedSystem = System()

        try:
            parsedSystem.parse(ast)
        except Exception, e :
            raise e
            
        return parsedSystem
    
################################################################################
################################################################################
################################################################################









class Types():
    SYSTEM = 0
    MODULE = 1
    BOOL = 2
    SET = 3
    RANGE = 4
    FAULT = 5
    LOCALVAR = 6
    NEXTVAL = 7
    NEXTREF = 8
    PROPFORM = 9
    MATH = 10
    IDENT = 11
    TRANS = 12
    PERMFAULT = 13
    INSTANCE = 14
    COMPASSION = 15
    FAIRNESS = 16
    LTLSPEC = 17
    inverse = { 
                0:'SYSTEM', 1:'MODULE', 2:'BOOL', 3:'SET', 4:'RANGE',
                5:'FAULT', 6:'LOCALVAR', 7:'NEXTVAL', 8:'NEXTREF', 9:'PROPFORM', 
                10:'MATH', 11:'IDENT', 12:'TRANS', 13:'PERMFAULT', 
                14:'INSTANCE', 15:'COMPASSION', 16:'FAIRNESS', 17:'LTLSPEC'
              }


class FallutoBaseElem():
    def __init__(self):
        self.name = ""
        self.line = None
        self.type = None
        self.val = None
    
    def printMe(self):
        print "Parser2.py", Types.inverse[self.type], \
        "default printMe():", self.name

    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
        Types.inverse[self.type]
    
    def __repr__(self):
        print "Parser2.py", Types.inverse[self.type], \
        "default __repr__():", self.name

#///////////////////////////////////////////////////////////////////////////////
#    FUNCIONES AUXILIARES
#///////////////////////////////////////////////////////////////////////////////




class counter ():
    count = 0
    def __init__(self):
        pass



"""
    Devuelve el AST limpio (lo que estaba escrito en el archivo de entrada, 
    sin lo que agrega PyPEG) y si check == True entonces chequea correctitud 
    en los tipos.
"""

debugTODO("Implemetar el checkeo de tipos.")

def cleanAST(ast = [], check = False, expect = None):
    ret = []
    if isinstance(ast, Symbol):
        ret += cleanAST(ast.what)
    elif isinstance(ast, unicode):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += cleanAST(x)
    return ret




#///////////////////////////////////////////////////////////////////////////////
#    Una clase por casi cada "cosa" interpretada:
#///////////////////////////////////////////////////////////////////////////////


"""
    Class that represents the whole system being chequed aswell as the
    contraints over the system and specifications to be checked on it.
    Call the parse method of this class to fill it up from a PyAST instance
    returned from the Interpreter in Interpreter.py.
"""
class System(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.SYSTEM
        self.modules = {}
        self.instances = {}
        self.ltlspecs = []
        self.contraints = []
        self.options = Options()
        self.commonprops = []

    def printMe(self):
        print "SYSTEM STARTS AT", self.line
        print "<MODULES>"
        for m in self.modules.itervalues():
            m.printMe()
        for i in self.instances.itervalues():
            print i
        for c in self.contraints:
            print c
        for l in self.ltlspecs:
            print l
    
    def parse(self, AST):
        if AST != []:
            self.line = AST[0].__name__.line
        for elem in AST:
            if elem.__name__ == "MODULE":
                m = Module()
                m.parse(elem)
                self.modules[m.name] = m
            elif elem.__name__ == "INSTANCE":
                i = Instance()
                i.parse(elem)
                self.instances[i.name] = i
            elif elem.__name__ == "LTLSPEC":
                l = LtlSpec()
                l.parse(elem)
                self.ltlspecs.append(l)
            elif elem.__name__ == "FAIRNESS":
                f = Fairness()
                f.parse(elem)
                self.contraints.append(f)
            elif elem.__name__ == "COMPASSION":
                c = Compassion()
                c.parse(elem)
                self.contraints.append(c)
            elif elem.__name__ == "OPTIONS":
                self.options.parse(elem)
            elif elem.__name__ == "PROPERTIE":
                p = CommonPropertie()
                p.parse(elem)
                self.commonprops.append(p)
            else:
                raise SyntaxError(elem)
        
        if self.instances == {}:
            raise NoInstancesError()




    #.......................................................................
class CommonPropertie(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.preconditions = []
        self.propertie = None
        
    def parse(self, AST):
    
        debugCURRENT(AST)
    
        self.line = AST.__name__.line
        AST = AST.what[0]
        self.type = AST.__name__

        
        for e in AST.what[:-1:]:
            self.preconditions.append(e)
        
        for e in AST.what[-1::]:
            self.propertie = cleanAST(e.what)
    
        debugRED( "Parsing propertie " + self.name + " at line "\
                   + str(self.line) \
                   + "\n\t@Preconditions: " + str(self.preconditions) \
                   + "\n\t@Propertie: " + str(self.propertie))






    #.......................................................................

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
        assert AST != []
        self.line = AST.__name__.line
        AST = AST.what # AST = [ name, contextvars, synchroacts, body]
        self.name = AST[0].what
        for v in AST[1].what:
            self.contextVars.append(v.what)
        for a in AST[2].what:
            self.synchroActs.append(a.what)

        for elem in AST[3].what:
            if elem.__name__ == "VAR":
                for v in elem.what:
                    var = LocalVar()
                    var.parse(v)
                    self.localVars.append(var)
            elif elem.__name__ == "INIT":
                self.init.append(cleanAST(elem.what, False))
            elif elem.__name__ == "FAULT":
                for f in elem.what:
                    fault = Fault()
                    fault.parse(f)
                    self.faults.append(fault)
            elif elem.__name__ == "TRANS":
                #reset de nn count atribute for unamed trans 
                Trans.nncount = 0
                for t in elem.what:
                    trans = Trans()
                    trans.parse(t)
                    self.trans.append(trans)
            else:
                raise SyntaxError

        debugYELLOW("Parsed module " + self.name + " at line " + self.line)

    def printMe(self):
        print "< Module >", self.name, "at", self.line
        print "< ContextVars >"
        for c in self.contextVars:
            print c,
        print "\n< SynchroActs >"
        for a in self.synchroActs:
            print a,
        print "\n< BODY >"
        print "< VAR >"
        for v in self.localVars:
            v.printMe()
        print "< INIT >"
        for i in self.init:
            print i
        print "< FAULT >"
        for f in self.faults:
            print f
        print "< TRANS >"
        for t in self.trans:
            print t


    #.......................................................................
    
"""
    Represents a transition between two states in Falluto.
"""
class Trans(FallutoBaseElem):

    #counter used to uniquely name unnamed transitions
    nncount = 0 
    
    def __init__ (self):
        FallutoBaseElem.__init__(self)
        self.type = Types.TRANS
        self.faults = []
        self.pre = PropForm()
        self.pos = []
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        for elem in AST:
            if elem.__name__ == 'IDENT':
                self.name = elem.what
            elif elem.__name__ == 'PROPFORM':
                self.pre.parse(elem)
            elif elem.__name__ == 'NEXTPROPFORM':
                for v in elem.what:
                    n = NextVal()
                    n.parse(v)
                    self.pos.append(n)
            else:
                raise SyntaxError(elem.__name__)
                
        if self.name == "":
            self.name = "nnact"+repr(self.nncount)
            Trans.nncount += 1
            
        # Empty preconditions represent an always true possibility of 
        # making the transition.
        if self.pre.val == []:
            self.pre.val = ['TRUE']
        
    def __repr__(self):
        return "< trans >: " + repr(self.name) + ": PRE: " + repr(self.pre) + \
               ": POS: " + repr(self.pos) + ": FAULTS: " + repr(self.faults)




    #.......................................................................
    
class LocalVar(FallutoBaseElem):
    def __init__ (self):
        FallutoBaseElem.__init__(self)
        self.domain = None
        self.type = Types.LOCALVAR

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what                # AST = IDENT, ":", [ BOOLEAN, SET, RANGE]
        self.name = AST[0].what
        if AST[1].__name__ == 'BOOLEAN':
            b = Bool()
            self.domain = b
        elif AST[1].__name__ == 'SET':
            s = Set()
            s.parse(AST[1])
            self.domain = s
        elif AST[1].__name__ == 'RANGE':
            r = Range()
            r.parse(AST[1])
            self.domain = r
        else:
            raise SyntaxError

    def printMe(self):
        print "< LocalVar >", self.name, ":", Types.inverse[self.type], \
            ":", self.domain
    
    #.......................................................................


"""
    Represents fault transitions between a normal or faulty state to a faulty
    state in Falluto.
"""
class Fault(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.pre = []
        self.pos = []
        self.type = Types.FAULT
        self.faulttype = ""
        self.efects = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what     # AST = IDENT, ":", 0, PROPFORM, ":", 0, NEXTPROPFORM
        self.name = AST[0].what
        for elem in AST[1::]:
            if elem.__name__ == 'PROPFORM':
                self.pre = cleanAST(elem)
            elif elem.__name__ == 'NEXTPROPFORM':
                for e in elem.what:
                    n = NextVal()
                    n.parse(e)
                    self.pos.append(n)
            elif elem.__name__ == 'FAULTTYPE':                
                elem = elem.what[0]
                self.faulttype = elem.__name__
                for efect in elem.what:
                    self.efects.append(efect.what)
            else:
                raise SyntaxError(elem) #debug (no deberia pasar nunca)
    
        # Empty preconditions represent an always true possibility of 
        # making the transition.
        if self.pre == []:
            self.pre = ['TRUE']

    def __repr__(self):
        string = "< Fault > " + self.name + " of type " + self.faulttype + \
            ": PRE: " + repr(self.pre) + " POS: " + repr(self.pos) + \
            " EFECTS: " + repr(self.efects)
        return string

    #.......................................................................
            
class NextVal(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.val = None
        self.type = Types.NEXTVAL

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.name = AST[0].what
        if AST[1].__name__ == 'SET':
            s = Set()
            s.parse(AST[1])
            self.val = s
        elif AST[1].__name__ == 'NEXTREF':
            n = NextRef()
            n.parse(AST[1])
            self.val = n
        elif AST[1].__name__ == 'MATH':
            m = Math
            m.parse(AST[1])
            self.val = m
        elif AST[1].__name__ == 'PROPFORM':
            p = PropForm()
            p.parse(AST[1])
            self.val = p
        elif AST[1].__name__ == 'IDENT':
            i = Ident()
            i.parse(AST[1])
            self.val = i
        elif AST[1].__name__ == 'RANGE':
            r = Range()
            r.parse(AST[1])
            self.val = r
        else:
            raise SyntaxError(AST[1].__name__)

    def __repr__(self):
        return self.name + ":" + repr(self.val) + " "


    #.......................................................................

class Ident(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.IDENT
    
    def parse(self, AST):
        self.line = AST.__name__.line
        self.name = AST.what

    def __repr__(self):
        return self.name


    #.......................................................................

class PropForm(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.PROPFORM
        self.val = []

    def parse(self, AST):
        self.line = AST.__name__.line
        self.val = cleanAST(AST.what)
    
    def __repr__(self):
        return repr(self.val)


    #.......................................................................

class Math(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = MATH
        self.val = None

    def parse(self, AST):
        self.line = AST.__name__.line
        self.val = cleanAST(AST.what)

    def __repr__(self):
        return repr(self.val)


    #.......................................................................

class NextRef(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.NEXTREF
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.name = AST[0].what
    
    def __repr__(self):
        return "next(" + repr(self.name) + ")"


    #.......................................................................

class Set(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.SET
        self.domain = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        for elem in AST:
            self.domain.append(elem.what)        

    def __repr__(self):
        return Types.inverse[self.type] + " : " + repr(self.domain)


    #.......................................................................

class Range(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.RANGE
        self.domain = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        for elem in AST:
            self.domain.append(elem.what)        

    def __repr__(self):
        return Types.inverse[self.type] + " : " + repr(self.domain)


    #.......................................................................

class Bool(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.BOOL
        self.domain = [ False, True]

    def parse(self):
        pass

    def __repr__(self):
        return Types.inverse[self.type] + " : " + repr(self.domain)


    #.......................................................................

class Instance(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.INSTANCE
        self.module = ""
        self.params = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.name = AST[0].what
        self.module = AST[1].what
        for v in AST[2].what:
            self.params.append(v)

    def __repr__(self):
        return "< INSTANCE >: " + self.name + ": " + "of module " + \
                self.module + ": Params " + repr(self.params)


    #.......................................................................

class LtlSpec(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.LTLSPEC
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.value = cleanAST(AST)
        
    def __repr__(self):
        return "< LTLSPEC >: " + repr(self.value)


    #.......................................................................

class Fairness(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.FAIRNESS
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.value = cleanAST(AST)
        
    def __repr__(self):
        return "< FAIRNESS >: " + repr(self.value)


    #.......................................................................

class Compassion(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.type = Types.COMPASSION
        self.pre = None
        self.pos = None
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.pre = cleanAST(AST[0])
        self.pos = cleanAST(AST[1])

    def __repr__(self):
        return "< COMPASSION >: Pre: " + repr(self.pre) + " Pos: " + \
                repr(self.pos)



    #.......................................................................
class Options(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.sysname = ""
        self.checkdeadlock = False
        self.faultsysfairdisable = False
        self.modulewfairdisable = False
    
    def parse(self, AST):
        self.line = AST.__name__.line
        for elem in AST.what:
            if elem.__name__ == "SYSNAME":
                self.sysname = elem.what[0]
            elif elem.__name__ == "CHECKDEADLOCK":
                self.checkdeadlock = True
            elif elem.__name__ == "FAULTSYSFAIRDISABLE":
                self.faultsysfairdisable = True
            elif elem.__name__ == "MODULEWFAIRDISABLE":
                self.modulewfairdisable = True
            else:
                raise SyntaxError(elem.__name__)







#                       EeEeEe   Nn    Nn   DdDdDd
#                       eE       nNnN  nN   dD   dD
#                       EeEe     Nn Nn Nn   Dd    Dd
#                       eE       nN  nNnN   dD   dD
#                       EeEeEe   Nn    Nn   DdDdDd


