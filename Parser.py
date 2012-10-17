################################################################################
# Module Parser.py
#
#
# Viernes 12 de Octubre 2012
# Raul Monti
#
#
################################################################################


from Debug import *
from Config import *
from Exceptions import *
from Types import Types
import pyPEG
from GrammarRules import GRAMMAR, COMMENT
import fileinput


################################################################################
################################################################################
################################################################################



def _cl(ast = []):
    """
        Devuelve una lista formada por los elementos de tipo unicode que estan 
        dentro del AST. 'ast' debe haber sido contruido por la funcion parse o 
        parseLine del modulo pyPEG o debe ser una subseccion del mismo, siempre y 
        cuando sea de tipo Symbol, list o unicode.
    """
    ret = []
    if isinstance(ast, pyPEG.Symbol):
        ret += _cl(ast.what)
    elif isinstance(ast, unicode):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += _cl(x)
    return ret



################################################################################

def _str(ast = []):
    """
        Devuelve un string formado por los elementos de tipo unicode que estan 
        dentro del AST separados entre ellos por espacios simples. 'ast' debe 
        haber sido contruido por la funcion parse o parseLine del modulo pyPEG 
        o debe ser una subseccion del mismo, siempre y cuando sea de tipo 
        Symbol, list o unicode.
    """
    lst = _cl(ast)
    string = ""
    if lst != []:
        string = str(lst[0])
    for element in lst[1::]:
        string += " " + str(element)
    return string




################################################################################


class ParserBaseElem():
    """
        Class to be enheritate when representing a parsed element.
        Los elementos interpretados por pyPEG llegan con la forma 
    """
    
    def __init__(self):
        self.name = ""   #
        self.type = None #
        self.line = ""   # string con al menos el numero de linea en donde se encuentra el elemento
        self.params = [] # lista de tipo pyAST
        self.ast = None  #TODO DEPRECATED 

    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
            str(self.__class__.__name__)

    def str(self):
        try:
            strg =_str(self.ast)
            return strg
        except:
            return ""

    def cl(self):
        try:
            lst = _cl(self.ast)
            return lst
        except:
            return []

    def __str__(self):
        return "Parser.py " + str(self.__class__.__name__) \
             + " default __repr__(): " + str(self.name)
        
    def __repr__(self):
        return repr(str(self))

    def __unicode__(self):
        return unicode(str(self))



################################################################################
def parse( _file):
    
    if _file == None:
        raise Exception("No file to parse :S")
       
    _ast = pyPEG.parse(GRAMMAR, _file, True, packrat = True)
    
    _res = System()
    
    _res.parse(_ast)
    
    return _res



################################################################################

class System(ParserBaseElem):
    """
        This class represents the full parsed system from the .fll file.
    """
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.modules = {}
        self.instances = {}
        self.properties = {}
        self.contraints = {}
        self.options = {}

    
    def clear(self):
        self.__init__()


    def parse(self, ast):
        ast = ast[0]
        assert ast.__name__ == "SYSTEM"
        self.clear()
        self.ast = ast
        for elem in ast.what:
            if elem.__name__ == "OPTIONS":
                for opt in elem.what:
                    o = Option()
                    o.parse(opt)
                    if o.name in self.options:
                        WARNING( "Redeclared option \'" + o.name \
                                + "\', using only last declaration.\n")
                    self.options[o.name] = o
            elif elem.__name__ == "MODULE":
                m = Module()
                m.parse(elem)
                if m.name in self.modules:
                    raise LethalException( "Redeclared module " + m.name \
                                         + " at line " + m.line + ".\n" )
                self.modules[m.name] = m
            elif elem.__name__ == "INSTANCE":
                i = Instance()
                i.parse(elem)
                if i.name in self.instances:
                    raise LethalException( "Redeclared instance " + i.name \
                                         + " at line " + i.line + ".\n" )
                self.instances[i.name] = i
            elif elem.__name__ == "SPECIFICATION":
                p = Propertie()
                p.parse(elem)
                assert not p.name in self.properties
                self.properties[p.name] = p
            elif elem.__name__ == "CONTRAINT":
                c = Contraint()
                c.parse(elem)
                assert not c.name in self.contraints
                self.contraints[c.name] = c
            else:
                assert False



    def __str__(self):
        string = "System " + self.name + " Parsed structure:\n\n"
        for m in self.modules.itervalues():
            string += str(m) + "\n"
        for i in self.instances.itervalues():
            string += str(i) + "\n"
        for p in self.properties.itervalues():
            string += str(p) + "\n"
        for c in self.contraints.itervalues():
            string += str(c) + "\n"
        for o in self.options.itervalues():
            string += str(o) + "\n"
        string += "\n" + self.name + "END ....................................."
        return string


################################################################################

class Option(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self, AST):
        self.ast = AST
        self.type = AST.__name__
        self.name = AST.what[0]
        self.params = AST.what[1::]
        self.line = AST.__name__.line
        
    def __str__(self):
        string = "\n---> Option " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string
        

################################################################################

class Module(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.contextvars = []
        self.synchroacts = []
        self.localvars   = []
        self.faults      = []
        self.init        = None
        self.transitions = []

    def parse(self, AST):
        self.ast = AST
        AST = AST.what # [ name, context vars, synchro acts, body ]
        self.name = AST[0].what[0]
        self.line = AST[0].__name__.line
        
        for cv in AST[1].what:
            self.contextvars.append(_str(cv))

        for sa in AST[2].what:
            self.synchroacts.append(_str(sa))

        AST = AST[3].what # [ 0, MODVAR, 0, MODFAULT, 0, MODINIT, 0, MODTRANS ]
        
        for elem in AST:
            if elem.__name__ == "MODVAR":
                for x in elem.what:
                    lv = LocalVar()
                    lv.parse(x)
                    self.localvars.append(lv)
            elif elem.__name__ == "MODFAULT":
                for x in elem.what:
                    f = Fault()
                    f.parse(x)
                    self.faults.append(f)
            elif elem.__name__ == "MODINIT":
                self.init = elem.what[0]
                debugRED("Esto deberia ser un pyAST: " + repr(self.init))
            elif elem.__name__ == "MODTRANS":
                for x in elem.what:
                    t = Transition()
                    t.parse(x)
                    self.transitions.append(t)
            else:
                assert False
                    


################################################################################

class Instance(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.module = "" # string name of the module map for this instance
        
    def parse(self, AST):
        AST = AST.what
        self.name = AST[0].what[0]
        self.line = AST[0].__name__.line
        self.module = _str(AST[1].what[0])

        for x in AST[2].what:
            self.params.append(x)
        
    def __str__(self):
        string = "\n---> Instances " + str(self.name)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string


################################################################################

class Propertie(ParserBaseElem):

    count = 0

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.formula = "" # the formula goes here, everything else in 'params'

    def parse(self, AST):
        AST = AST.what[0]
        self.name = "prop" + str(Propertie.count)
        Propertie.count += 1
        self.line = AST.__name__.line
        self.type = AST.__name__
        
        self.formula = AST.what[-1].what
        for f in AST.what[:-1:]:
            self.params.append(f)
 
 
    def __str__(self):
        string = "\n---> Propertie " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        string += "; and formula " + str(self.formula)
        return string


################################################################################

class Contraint(ParserBaseElem):

    count = 0

    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self, AST):
        self.name = "contraint" + str(Contraint.count)
        Contraint.count += 1
        AST = AST.what[0]
        self.type = AST.__name__
        self.line = AST.what[0].__name__.line
        for x in AST.what:
            self.params.append(x)

    def __str__(self):
        string = "\n---> Contraint: " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters: " + str(self.params)
        return string
        


################################################################################

class LocalVar(ParserBaseElem):
    
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.domain = []
    
    def parse(self, AST):
        AST = AST.what # [name, domain]
        self.name = _str(AST[0])
        self.line = AST[0].__name__.line
        AST = AST[1]
        if AST.__name__ == "BOOLEAN":
            self.type = Types.Bool
        elif AST.__name__ == "SET":
            self.type = Types.Symbol
            for x in AST.what:
                self.domain.append(_str(x))
        elif AST.__name__ == "RANGE":
            self.type = Types.Int
            for x in AST.what:
                self.domain.append(_str(x))
        else:
            assert False

    def __str__(self):
        return ParserBaseElem.__str__(self)

################################################################################

class Fault(ParserBaseElem):
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre     = None
        self.pos     = None
        self.affects = []

    def parse(self, AST):
        AST = AST.what # [name, pre, pos, type]
        self.name = _str(AST[0])
        self.line = AST[0].__name__.line
        self.pre = AST[1]
        self.pos = AST[2]
        AST = AST[3]
        self.type = AST.__name__
        for x in AST.what:
            self.affects.append(_str(x))

    def __str__(self):
        return ParserBaseElem.__str__(self)

################################################################################

class Transition(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre = None
        self.pos = None

    def parse(self, AST):
        debugRED(AST)
        self.line = str(AST.__name__.line)
        AST = AST.what # [0, name, 0, pre, 0,pos]
        for elem in AST:
            if elem.__name__ == "IDENT":
                self.name = _str(elem)
            elif elem.__name__ == "SIMPLEXPR":
                self.pre = elem                
            elif elem.__name__ == "NEXTEXPR":
                self.pos = elem
            else:
                assert False
        
    def __str__(self):
        return ParserBaseElem.__str__(self)
################################################################################





# TESTS ........................................................................
if __name__ == "__main__":

    _file = fileinput.input()

    _sys = parse(_file)
 
    debugGREEN(_sys)


