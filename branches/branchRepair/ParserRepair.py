#===============================================================================
# Module Parser.py
#
#
# Martes 23 de Octubre 2012
# Raul Monti
#
#
#===============================================================================
#
from DebugRepair import *
from ConfigRepair import *
from Exceptions import *
from Types import Types
import pyPEG
from GrammarRulesRepair import GRAMMAR, COMMENT, EXPRESION
import fileinput
from Utils import _cl, _str, getBestLineNumberForExpresion
import Utils
import shutil
import os.path
import sys
import os
#
#===============================================================================

# Auxiliary functions

def getTrueExpresion():
    string = "TRUE"
    ast = pyPEG.parseLine(string, EXPRESION,[],True,COMMENT)
    return ast[0][0]


#===============================================================================



################################################################################
################################################################################

class ParserBaseElem(object):
    """
        Class to be enheritate when representing a parsed element.
    """
    #.......................................................................
    def __init__(self):
        self.name = ""   #
        self.type = None #
        self.line = ""   # string whith at least the line number of the element.
        self.params = []
        self.rawinput = None
    #.......................................................................
    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
            str(self.__class__.__name__)
    #.......................................................................
    def str(self):
        try:
            strg =_str(self.rawinput)
            return strg
        except:
            return ""
    #.......................................................................
    def cl(self):
        try:
            lst = _cl(self.rawinput)
            return lst
        except:
            return []
    #.......................................................................
    def __str__(self):
        return "Parser.py " + str(self.__class__.__name__) \
             + " default __repr__(): " + str(self.name)
    #.......................................................................
    def __repr__(self):
        return object.__repr__(self) + " <" + self.name + "> "
    #.......................................................................
    def __unicode__(self):
        return unicode(str(self))
    #.......................................................................


################################################################################
################################################################################
def parse(filePath = None):
    """
        Use PyPEG to parse de file into a PyPEG structure. Use this structure
        to fill up our specific structures which are easier to work with.
    """

    if _file == None or not os.path.isfile(filePath):
        raise Exception("Path <"+ str(filePath) +"> is not a valid file to " +\
                        "parse :S.")

    # get a copy of the original file and prepare it for pyPEG.
    backup = TEMP_DIR__+'/'+(_file.split('/')[-1]).split('.')[0]+".fllaux"

    debug('debugLBLUE', "backup file: "+ backup)

    shutil.copy2(_file, backup)
    try:
        # If something goes wrong we should be sure to remove the backup file
        # and recover the original one.
        f = open(_file, 'a')
        f.write("//Line to avoid problems with pyPEG line count.")
        f.close()

        # packrat = True seems to be brocken :S TODO check if it is
        debug('debugGREEN',"Parsing ...")
          

        _ast = pyPEG.parse(GRAMMAR, 
                           fileinput.input(_file), 
                           True, 
                           COMMENT, 
                           packrat = False)
        # recover original file
        shutil.copy2(backup, _file)
        os.remove(backup)        
    except Exception, e:
        # recover original file
        shutil.copy2(backup, _file)
        os.remove(backup)
        raise e
    # get everything inside our structures:
    _res = System()
    
    print "Going out here ..."
    exit(0)

    _res.parse(_ast[0])

    return _res


################################################################################
################################################################################
class System(ParserBaseElem):
    """
        This class represents the full parsed model from the .fll file.
    """
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.defines    = {}
        self.proctypes  = {}
        self.instances  = {}
        self.properties = {}
        self.contraints = {}
        self.options    = {}


    #.......................................................................
    def clear(self):
        self.__init__()

    #.......................................................................
    def parse(self, ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "SYSTEM"
        self.clear()
        self.rawinput = ast
        for elem in ast.what:
            if elem.__name__ == "OPTIONS":
                for opt in elem.what:
                    if opt.__name__ == "SYSNAME":
                        self.name = _str(opt.what)
                    else:
                        o = Option()
                        o.parse(opt)
                        if o.name in self.options:
                            WARNING( "Redeclared option \'" + o.name \
                                    + "\', using only last declaration.\n")
                        self.options[o.name] = o
            elif elem.__name__ == "DEFINE":
                d = Define()
                d.parse(elem)
                d.name = "define" + str(len(self.defines))
                self.defines[d.name] = d
            elif elem.__name__ == "PROCTYPE":
                p = Proctype()
                p.parse(elem)
                if p.name in self.proctypes:
                    raise LethalE( "Redeclared proctype " + p.name \
                                         + " at line " + p.line + ".\n" )
                self.proctypes[p.name] = p
            elif elem.__name__ == "INSTANCE":
                i = Instance()
                i.parse(elem)
                if i.name in self.instances:
                    raise LethalE( "Redeclared instance \'" + i.name \
                                         + "\' at <" + i.line + ">.\n" )
                self.instances[i.name] = i
            elif elem.__name__ == "SPECIFICATION":
                p = Propertie()
                p.parse(elem)
                p.name = "propertie" + str(len(self.properties))
                assert not p.name in self.properties
                self.properties[p.name] = p
            elif elem.__name__ == "CONTRAINT":
                c = Contraint()
                c.parse(elem)
                c.name = "contraint" + str(len(self.contraints))
                assert not c.name in self.contraints
                self.contraints[c.name] = c
            else:
                assert False


    #.......................................................................
    def __str__(self):
        string = "System " + self.name + " Parsed structure:\n\n"
        for m in self.proctypes.itervalues():
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
    #.......................................................................



################################################################################

class Option(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
    #.......................................................................
    def parse(self, AST):
        self.rawinput = AST
        self.name = AST.what[0]
        self.params = AST.what[1::]
        self.line = AST.__name__.line
        if AST.__name__ == "MODULEWFAIRDISABLE":
            self.type = Types.WFDisable
        elif AST.__name__ == "FAULTFAIRDISABLE":
            self.type = Types.FFDisable
        elif AST.__name__ == "CHECKDEADLOCK":
            self.type = Types.Checkdk
        elif AST.__name__ == "SYSNAME":
            self.type = Types.Sysname
        else:
            debugWARNING("Bad option " + str(AST.__name__))
            
     #.......................................................................
    def __str__(self):
        string = "\n---> Option " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string
    #.......................................................................


################################################################################
class Define(ParserBaseElem):
    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self,ast):
        self.line = Utils.getBestLineNumberForExpresion(ast)
        self.dname = ast.what[0]
        self.dvalue = ast.what[1]

        
################################################################################

class Proctype(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.contextvars     = []
        self.synchroacts     = []
        self.localvars       = []
        self.faults          = []
        self.init            = None
        self.transitions     = []
        self.transitioncount = 0

    #.......................................................................
    def parse(self, AST):
        self.rawinput = AST
        AST = AST.what # [ name, context vars, synchro acts, body ]
        self.name = AST[0].what[0]
        self.line = AST[0].__name__.line
        
        for cv in AST[1].what:
            self.contextvars.append(cv)

        for sa in AST[2].what:
            self.synchroacts.append(sa)

        AST = AST[3].what # [ 0, VAR, 0, FAULT, 0, INIT, 0, TRANS ]
        
        for elem in AST:
            if elem.__name__ == "VAR":
                for x in elem.what:
                    lv = VarDeclaration()
                    lv.parse(x)
                    self.localvars.append(lv)
            elif elem.__name__ == "FAULT":
                for x in elem.what:
                    f = Fault()
                    f.parse(x)
                    self.faults.append(f)
            elif elem.__name__ == "INIT":
                if elem.what != []:
                    self.init = elem.what[0]
                else:
                    self.init = getTrueExpresion()
                    self.init.__name__.file = elem.__name__.file
                    self.init.__name__.line = elem.__name__.line
            elif elem.__name__ == "TRANS":
                for x in elem.what:
                    t = Transition()
                    t.parse(x)
                    if t.name == "":
                        # Is a transition without name, we give it one.
                        t.name = "NN#" + str(self.transitioncount)
                        self.transitioncount += 1
                    t.pc = len(self.transitions)
                    self.transitions.append(t)
            else:
                assert False

    #.......................................................................
    def __str__(self):
        string = ""
        for f in self.faults:
            string += str(f) + "\n"
        for v in self.localvars:
            string += str(v) + "\n"
        return string
    #.......................................................................

################################################################################

class Instance(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.proctype = "" # string name of the proctype for this instance
    #.......................................................................
    def parse(self, AST):
        AST = AST.what # [ name, proctype name, parameters list]
        self.name = AST[0].what[0]
        self.line = getBestLineNumberForExpresion(AST)
        self.proctype = _str(AST[1])

        for x in AST[2].what:
            self.params.append(x)
    #.......................................................................
    def __str__(self):
        string = "\n---> Instances " + str(self.name) 
        string += " of proctype " + str(self.proctype)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string
    #.......................................................................


################################################################################

class Propertie(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.formula = "" # the formula goes here, everything else in 'params'
    #.......................................................................
    def parse(self, AST):
        AST = AST.what[0]
        self.line = AST.__name__.line
        self.type = Types.propToType[AST.__name__]

        self.formula = AST.what[-1]
        for f in AST.what[:-1:]:
            self.params.append(f)
 
    #.......................................................................
    def __str__(self):
        string = "\n---> Propertie " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        string += "; and formula " + str(self.formula)
        return string
    #.......................................................................

################################################################################

class Contraint(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
    #.......................................................................
    def parse(self, AST):
        AST = AST.what[0]
        self.type = AST.__name__
        self.line = AST.what[0].__name__.line
        for x in AST.what:
            self.params.append(x)
    #.......................................................................
    def __str__(self):
        string = "\n---> Contraint: " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters: " + str(self.params)
        return string
    #.......................................................................


################################################################################

class VarDeclaration(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.range = []
        self.domain = []
        self.isarray = False
    #.......................................................................
    def parse(self, AST):
        self.rawinput = AST
        AST = AST.what # [name, domain]
        self.name = _str(AST[0])
        self.line = AST[0].__name__.line
        AST = AST[2]
        if AST.__name__ == "BOOLEAN":
            self.type = Types.Bool
        elif AST.__name__ == "ENUM":
            self.type = Types.Symbol
            for x in AST.what:
                if not isinstance(x, unicode):
                    self.domain.append(_str(x))
        elif AST.__name__ == "RANGE":
            self.type = Types.Int
            for x in AST.what:
                if not isinstance(x, unicode):
                    self.domain.append(_str(x))
        elif AST.__name__ == "ARRAY":
            self.isarray = True
            self.range.append(_str(AST.what[1]))
            self.range.append(_str(AST.what[3]))
            domain = AST.what[5]
            if domain.__name__ == "BOOLEAN":
                self.type = Types.Bool
            elif domain.__name__ == "ENUM":
                self.type = Types.Symbol
                for x in domain.what:
                    if not isinstance(x, unicode):
                        self.domain.append(_str(x))
            elif domain.__name__ == "RANGE":
                self.type = Types.Int
                for x in domain.what:
                    if not isinstance(x, unicode):
                        self.domain.append(_str(x))
            else:
                raise TypeError(domain)
        else:
            raise TypeError(domain)


    #.......................................................................
    def __str__(self):
        string = "---> Variable " + str(self.name) + " declaration"
        string += ", of type " + Types.Types[self.type]
        string += ", and domain values: "
        for x in self.domain:
            string += "<" + str(x) + "> "
        return string
    #.......................................................................


################################################################################

class Fault(ParserBaseElem):
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre     = None
        self.pos     = []
        self.affects = []
    #.......................................................................
    def parse(self, AST):
        AST = AST.what # [name, pre, pos, type]
        self.line = AST[0].__name__.line
        for x in AST:
            if x.__name__ == "NAME":
                self.name = _str(x)
            elif x.__name__ == "EXPRESION":
                self.pre = x
            elif x.__name__ == "NEXTEXPR":
                for elem in x.what:
                    elem = elem.what
                    nextref = elem[0]
                    symbol = elem[1]
                    expr = elem[2]
                    self.pos.append([nextref, symbol, expr])
            elif x.__name__ in ["BYZ", "STOP", "TRANSIENT"]:
                if x.__name__ == "BYZ":
                    self.type = Types.Byzantine
                elif x.__name__ == "STOP":
                    self.type = Types.Stop
                else:
                    self.type = Types.Transient
                for y in x.what:
                    self.affects.append(y)
        if self.pre == None or self.pre == "":
            self.pre = getTrueExpresion()
            self.pre.file = AST[0].__name__.file
            self.pre.line = AST[0].__name__.line
    #.......................................................................
    def __str__(self):
        string = "--> Fault \'" + str(self.name)
        string += "\'\n @Type >> " + str(self.type)
        string += "\n @Pre >> " + str(self.pre)
        string += "\n @Pos >> " + str(self.pos)
        string += "\n @Affects >>" + str(self.affects)
        return string
    #.......................................................................


################################################################################

class Transition(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre = None
        self.pos = []
        self.pc = 0 # program counter number used for compilation
    #.......................................................................
    def parse(self, AST):
        line = str(AST.__name__.line)
        mfile = str(AST.__name__.file)
        self.line = line
        AST = AST.what # [0, name, 0, pre, 0,pos]
        for elem in AST:
            if elem.__name__ == "NAME":
                self.name = _str(elem)
            elif elem.__name__ == "EXPRESION":
                self.pre = elem
            elif elem.__name__ == "NEXTEXPR":
                for x in elem.what:
                    x = x.what
                    nextref = x[0]
                    symbol = x[1]
                    expr = x[2]
                    self.pos.append([nextref, symbol, expr])
            else:
                assert False

        if self.pre == None or self.pre == "":
            self.pre = getTrueExpresion()
            self.pre.file = mfile
            self.pre.line = line

    #.......................................................................
    def __str__(self):
        return ParserBaseElem.__str__(self)
    #.......................................................................
################################################################################





# TESTS ........................................................................
if __name__ == "__main__":

    wd = os.getcwd()
    _file = sys.argv[1]
    _file = os.path.join(os.getcwd(), _file)
    debug('debugLBLUE', "original file: " + _file)

    _sys = parse(_file)

    print str(_sys)


