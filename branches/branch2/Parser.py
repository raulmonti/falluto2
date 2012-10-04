################################################################################
# Module Parser.py
#
#
# Lun 24 de Septiembre 2012
# Raul Monti
#
#
################################################################################


from Debug import *
from Config import *
from Exceptions import *
from TypeSystem import Types
import pyPEG
from GrammarRules import GRAMMAR, COMMENT




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
        
        ast = pyPEG.parse(GRAMMAR, inputFile, True, COMMENT, lineCount = True)
        parsedSystem = FallutoSystem()  
        parsedSystem.parse(ast)

        return parsedSystem
    
################################################################################
################################################################################
################################################################################



class FallutoBaseElem():

    def __init__(self):
        self.name = ""
        self.line = None
        self.type = None
        self.value = None
    
    def printMe(self):
        print "Parser2.py",  str(self.__class__.__name__), \
        "default printMe():", self.name

    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
            str(self.__class__.__name__)
    
    def __repr__(self):
        return "Parser.py " + str(self.__class__.__name__) \
             + " default __repr__(): " + str(self.name)



"""
    Devuelve el AST limpio (lo que estaba escrito en el archivo de entrada, 
    sin lo que agrega PyPEG)
"""
def _cl(ast = []):
    ret = []
    if isinstance(ast, Symbol):
        ret += _cl(ast.what)
    elif isinstance(ast, unicode):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += _cl(x)
    return ret




#///////////////////////////////////////////////////////////////////////////////
#    Una clase por casi cada "cosa" interpretada:
#///////////////////////////////////////////////////////////////////////////////
        

"""
    Class that represents the whole system being chequed aswell as the
    contraints over the system and specifications to be checked on it.
    Use the Parser class to parse a Falluto input file and get a FallutoSystem
    class with the resulting parsed system.
"""
class FallutoSystem(FallutoBaseElem):

    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.modules = {}
        self.instances = {}
        self.specifications = []
        self.contraints = []
        self.options = Options()


    def printMe(self):
        print "SYSTEM", self.name, "STARTS AT", self.line
        print self.options
        print "<MODULES>"
        for m in self.modules.itervalues():
            m.printMe()
        for i in self.instances.itervalues():
            print i
        for c in self.contraints:
            print c
        for l in self.specifications:
            print l

    
    def parse(self, AST):
    
        if AST == []:
            raise EmptyASTError()
        else:
            self.line = AST[0].__name__.line
            AST = AST[0].what

            for elem in AST:
                if elem.__name__ == "MODULE":
                    m = Module()
                    m.parse(elem)
                    self.modules[m.name] = m
                elif elem.__name__ == "INSTANCE":
                    i = Instance()
                    i.parse(elem)
                    self.instances[i.name] = i
                elif elem.__name__ == "SPECIFICATION":
                    s = Specification()
                    s.parse(elem)
                    self.specifications.append(s)
                elif elem.__name__ == "CONTRAINT":
                    c = Contraint()
                    c.parse(elem)
                    self.contraints.append(c)
                elif elem.__name__ == "OPTIONS":
                    self.options.parse(elem)
                else:
                    raise SyntaxError(elem)

            debugTODO("Sacar este chequeo de aca")
            if self.instances == {}:
                raise NoInstancesError()

    def __repr__(self):
        self.printMe()
        return ""




    #.......................................................................
    
class Module(FallutoBaseElem):

    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.contextVars = []
        self.synchroActs = []
        self.localVars = []
        self.init = []
        self.faults = []
        self.trans = []


    def parse(self, AST):
        assert AST != []
        AST = AST.what # AST = [ name, contextvars, synchroacts, body]
        self.name = AST[0].what
        self.line = AST[0].__name__.line
        for v in AST[1].what:
            self.contextVars.append(v.what)
        for a in AST[2].what:
            self.synchroActs.append(a.what)

        for elem in AST[3].what:
            if elem.__name__ == "MODVAR":
                for v in elem.what:
                    var = LocalVar()
                    var.parse(v)
                    self.localVars.append(var)
            elif elem.__name__ == "MODFAULT":
                for f in elem.what:
                    fault = Fault()
                    fault.parse(f)
                    self.faults.append(fault)
            elif elem.__name__ == "MODINIT":
                debugYELLOW("Adding the following INIT to ths system: " + str(elem.what[0]))
                self.init.append(elem.what[0])
            elif elem.__name__ == "MODTRANS":
                #reset de nn count atribute for unamed trans 
                Trans.nncount = 0
                for t in elem.what:
                    trans = Trans()
                    trans.parse(t)
                    self.trans.append(trans)
            else:
                raise SyntaxError(elem.__name__)

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
    
class LocalVar(FallutoBaseElem):
    def __init__ (self):
        FallutoBaseElem.__init__(self)
        self.domain = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what                # AST = IDENT, ":", [ BOOLEAN, SET, RANGE]
        self.name = AST[0].what     
        domain = AST[1]
        if domain.__name__ == 'BOOLEAN':
            self.type = Types.Bool
        elif domain.__name__ == 'SET':
            self.type = Types.Symbol
        elif domain.__name__ == 'RANGE':
            self.type = Types.Int
        else:
            raise SyntaxError
        domain = domain.what
        debugCURRENT("Parsing domain for local variable:")
        debugCURRENT(domain)
        for elem in domain:
            self.domain.append(elem)          



    def printMe(self):
        print "< LocalVar >", self.name, ":", self.type, \
            ":", self.domain




    #.......................................................................
"""
    Represents fault transitions between a normal or faulty state to a faulty
    state in Falluto.
"""
class Fault(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.pre = None
        self.pos = []
        self.affects = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what     
        # AST = IDENT, ":", 0, SIMPLEXPR, 0, ("=>", NEXTEXPR), "is", FAULTTYPE
        self.name = AST[0].what
        for elem in AST[1::]:
            if elem.__name__ == 'BOOLPROP':
                self.pre = elem
            elif elem.__name__ == 'NEXTEXPR':
                for e in elem.what:
                    self.pos.append(e)
            elif elem.__name__ == 'FAULTTYPE':                
                elem = elem.what[0]
                self.type = elem.__name__
                for efect in elem.what:
                    self.affects.append(efect)
            else:
                raise SyntaxError(elem) #debug (no deberia pasar nunca)
    
        # Empty preconditions represent an always true possibility of 
        # making the transition.
        if self.pre == []:
            self.pre = ['TRUE']

        debugLBLUE("Parsed:" + repr(self))

    def __repr__(self):
        string = "< Fault > " + repr(self.name) + " of type " + repr(self.type)\
               + "\n\t@ PRE: " + repr(self.pre) + "\n\t@ POS: "\
               + repr(self.pos) + "\n\t@ AFFECTS: " + repr(self.affects)
        return string


    #.......................................................................
    
"""
    Represents a transition between two states in Falluto.
"""
class Trans(FallutoBaseElem):

    #counter used to uniquely name unnamed transitions
    nncount = 0 
    
    def __init__ (self):
        FallutoBaseElem.__init__(self)
        self.pre = None
        self.pos = []
    
    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        for elem in AST:
            if elem.__name__ == 'IDENT':
                self.name = elem.what
            elif elem.__name__ == 'BOOLPROP':
                self.pre = elem
            elif elem.__name__ == 'NEXTEXPR':
                for v in elem.what:
                    self.pos.append(v)
            else:
                raise SyntaxError(elem.__name__)
                
        if self.name == "":
            self.name = "nnact"+repr(self.nncount)
            Trans.nncount += 1
            
        # Empty preconditions represent an always true possibility of 
        # making the transition.
        if self.pre == []:
            self.pre = ['TRUE']
            
        debugLBLUE("Parsed: " + repr(self))
        
    def __repr__(self):
        return "< trans >: " + repr(self.name) + ": PRE: " + repr(self.pre) + \
               ": POS: " + repr(self.pos)





    #.......................................................................

class Instance(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.module = ""
        self.params = []

    def parse(self, AST):
        self.line = AST.__name__.line
        AST = AST.what
        self.name = AST[0].what
        self.module = AST[1].what
        for v in AST[2].what:
            self.params.append(v)

        debugGREEN("Parsed: " + repr(self))

    def __repr__(self):
        return "< INSTANCE >: " + self.name + ": " + "of module " + \
                self.module + "\n\t@ Params " + repr(self.params)



    ########################################################################
class Specification(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)

    def parse(self, AST):
        assert AST != []
        self.line = AST.__name__.line
        AST = AST.what[0]
        self.type = AST.__name__
        self.value = AST.what[0]
        
        debugGREEN("Parsed: " + str(self))

    def __repr__(self):
        return "< SPECIFICATION >" + " of type " + str(self.type) \
                + "\n\t@ value: " + str(self.value)




    ########################################################################
class Contraint(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.value = []
        
    def parse(self, AST):
        assert AST != []
        self.line = AST.__name__.line
        AST = AST.what[0]
        self.type = AST.__name__
        for elem in AST.what:
            self.value.append(elem)

        debugGREEN("Parsed: " + str(self))

    def __repr__(self):
        return "< CONTRAINT >" + " of type " + str(self.type) \
                + "\n\t@ value: " + str(self.value)





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





    #.......................................................................
    """
        Common properties can be better parsed using this class. They aren't
        nicely parsed in the FallutoSystem class.
    """
class CommonPropertie(FallutoBaseElem):
    def __init__(self):
        FallutoBaseElem.__init__(self)
        self.preconditions = []
        self.propertie = None
        
    def parse(self, AST):
    
        self.line = AST.__name__.line
        self.type = AST.__name__
        
        for e in AST.what[:-1:]:
            self.preconditions.append(e)
        
        for e in AST.what[-1::]:
            self.propertie = cleanAST(e.what)
    
        debugGREEN( "Parsing propertie " + self.name + " at line "\
                   + str(self.line) \
                   + "\n\t@Preconditions: " + str(self.preconditions) \
                   + "\n\t@Propertie: " + str(self.propertie))



import sys, os, fileinput

if __name__ == "__main__":

    parser = Parser()
    _file = fileinput.input()
    sys = parser.parse(_file)
    print sys



