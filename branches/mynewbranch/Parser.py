#===============================================================================
# Module Parser.py
#
#
# Martes 23 de Octubre 2012
# Raul Monti
#
#
#===============================================================================


import Debug
from Debug import *
from Config import *
from Exceptions import *
from Types import Types
import pyPEG
from pyPEG import Symbol
from GrammarRules import GRAMMAR, COMMENT, EXPRESION
import fileinput
from Utils import cleanAst, ast2str, getBestLineNumberForExpresion, getAst
from Utils import clearAst
import Utils
import shutil
import os.path
import sys
import os


#===============================================================================


################################################################################

def parse(filePath = None):
    """ Use PyPEG to parse de file into a PyPEG structure. Use this structure
        to fill up our specific structures which are easier to work with.
        Returns a 'Model' instance with the parsed model.
        
        @input filePath: the path of the file to be parsed
    """
    if filePath == None or not os.path.isfile(filePath):
        raise Error( "Path <"+ str(filePath) +"> is not a valid file to "\
                   + "parse :S.")
    # get a copy of the original file and prepare it for pyPEG.
    _backup = TEMP_DIR__+'/'+(filePath.split('/')[-1]).split('.')[0]+".fllaux"
    LDEBUG("User original file backup at: "+ _backup)
    shutil.copy2(filePath, _backup)
    try:
        # If something goes wrong we should be sure to remove the backup file
        # and recover the original one.
        _f = open(filePath, 'a')
        _f.write("//Line to avoid problems with pyPEG line count.")
        _f.close()
        # packrat = True seems to be brocken :S TODO check if it is
        LDEBUG("Parsing ...")
        _ast = pyPEG.parse(GRAMMAR, 
                           fileinput.input(filePath), 
                           True, 
                           COMMENT, 
                           packrat = False)
        # recover original file
        shutil.copy2(_backup, filePath)
        os.remove(_backup)        
    except Exception, _e:
        # recover original file
        shutil.copy2(_backup, filePath)
        os.remove(_backup)
        raise Error(str(_e))
    # get everything inside our Model structure:
    _res = Model()
    _res.parse(_ast[0])
    return _res


# Auxiliary functions #########################################################

def getTrueExpresion():
    string = "True"
    ast = pyPEG.parseLine(string, EXPRESION,[],True,COMMENT)
    return ast[0][0]


#===============================================================================

################################################################################

class ParserBaseElem(object):
    """
        Class to be enheritate when representing a parsed element.
    """

    def __init__(self):
        self.name = ""   #
        self.type = None #
        self.line = ""   # string whith at least the line number of the element.
        self.params = []
        self.pypeg = None

    def parse(self, AST):
        print "@.@ There is no parser method implemented for", \
            str(self.__class__.__name__)

    def str(self):
        try:
            strg = ast2str(self.pypeg)
            return strg
        except:
            return ""

    def cl(self):
        try:
            lst = _cl(self.rawinput)
            return lst
        except:
            return []

    def __str__(self):
        return "Parser.py " + str(self.__class__.__name__) \
             + " default __repr__(): " + str(self.name)

    def __repr__(self):
        return object.__repr__(self) + " <" + self.name + "> "

    def __unicode__(self):
        return unicode(str(self))

################################################################################

class Model(ParserBaseElem):
    """ The full model structure.
        This class represents the full parsed model from the .fll. Take a look
        at the 'parse' function in this module to be able to fill up this
        structure.
    """

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.defs       = {}
        self.proctypes  = {}
        self.instances  = {}
        self.properties = {}
        self.contraints = {}
        self.options    = {}

    def clear(self):
        """ Completely clean this structure to it's original values. """
        self.__init__()

    def parse(self, ast):
        """ Read the model from a pyPEG.Symbol instance containing the
            pyPEG parsed model, and fill up this structure.

            @input ast: the pyPEG.Symbol structure with the model information.

            @contraint: 'ast' should have been parsed using the 'GRAMMAR' rule
                        from GrammarRules.py.
        """
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "MODEL"
        self.clear()
        self.pypeg = ast
        for elem in ast.what:
            if elem.__name__ == "OPTIONS":
                for opt in [x for x in elem.what if isinstance(x,pyPEG.Symbol)]:
                    if opt.__name__ == "MODNAME":
                        self.name = ast2str(opt.what)
                    else:
                        o = Option()
                        o.parse(opt)
                        if o.name in self.options:
                            WARNING( "Redeclared option \'" + o.name \
                                    + "\', using only the last declaration.\n")
                        self.options[o.name] = o
            elif elem.__name__ == "DEFINE":
                d = Define()
                d.parse(elem)
                d.name = "define" + str(len(self.defs))
                self.defs[d.name] = d
            elif elem.__name__ == "PROCTYPE":
                p = Proctype()
                p.parse(elem)
                if p.name in self.proctypes:
                    raise Error( "Redeclared proctype " + p.name \
                                 + " at line " + p.line + ".\n" )
                self.proctypes[p.name] = p
            elif elem.__name__ == "INSTANCE":
                i = Instance()
                i.parse(elem)
                if i.name in self.instances: #TODO is this the place to check?
                    raise Error( "Redeclared instance \'" + i.name \
                                 + "\' at <" + i.line + ">.\n" )
                self.instances[i.name] = i
            elif elem.__name__ == "PROPERTY":
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

    def __str__(self):
        string = "> Model <" + self.name + "> parsed structure:\n\n"
        for i in self.defs.itervalues():
            string += str(i) + "\n"
        for m in self.proctypes.itervalues():
            string += str(m) + "\n"
        for i in self.instances.itervalues():
            string += str(i) + "\n\n"
        for p in self.properties.itervalues():
            string += str(p) + "\n\n"
        for c in self.contraints.itervalues():
            string += str(c) + "\n\n"
        for o in self.options.itervalues():
            string += str(o) + "\n\n"
        string += "> End model <" + self.name + "> parsed structure."
        return string

################################################################################

class Option(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)

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

    def __str__(self):
        string = ">> Option " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string

################################################################################

class Define(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self,ast):
        self.line = Utils.getBestLineNumberForExpresion(ast)
        ast = clearAst(ast.what)
        self.dname = ast[0]
        self.dvalue = ast[1]

    def __str__(self):
        _string = ">> Define <" + ast2str(self.dname) + ">"
        _string += " @value: " + ast2str(self.dvalue)
        return _string

################################################################################

class Proctype(ParserBaseElem):
    """ A proctype structure for parsing proctypes :P """

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.contextvars     = []
        self.synchroacts     = []
        self.localvars       = []
        self.faults          = []
        self.init            = None
        self.transitions     = []
        self.transitioncount = 0

    def parse(self, AST):
        self.rawinput = AST
        AST = AST.what # [ name, context vars, synchro acts, body ]
        self.name = AST[1].what[0]
        self.line = AST[1].__name__.line

        for cv in getAst(getAst(AST,["CTXVARS"])[0],["NAME"]):
            self.contextvars.append(ast2str(cv))

        for sa in getAst(getAst(AST,["SYNCACTS"])[0],["NAME"]):
            self.synchroacts.append(ast2str(sa))

        AST = getAst(AST,["PROCTYPEBODY"])[0]

        for elem in AST.what:
            if elem.__name__ == "VAR":
                for x in [y for y in elem.what if isinstance(y,Symbol) \
                          and y.__name__ == u'VARDECL']:
                    _lv = VarDeclaration()
                    _lv.parse(x)
                    self.localvars.append(_lv)
            elif elem.__name__ == "FAULT":
                for x in [y for y in elem.what if isinstance(y,Symbol) \
                          and y.__name__ == u'FAULTDECL']:
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
                for x in [y for y in elem.what if isinstance(y,Symbol) \
                          and y.__name__ == u'TRANSITION']:
                    t = Transition()
                    t.parse(x)
                    if t.name == "":
                        # Is a transition without name, we give it one.
                        t.name = "NN#" + str(self.transitioncount)
                        self.transitioncount += 1
                    t.pc = len(self.transitions)
                    self.transitions.append(t)
            elif elem.__name__ == "BL":
                pass
            else:
                assert False

    def __str__(self):
        string = ">> Proctype " + self.name + '\n'
        for f in self.faults:
            string += str(f) + '\n'
        for v in self.localvars:
            string += str(v) + '\n'
        return string


################################################################################

class Instance(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.proctype = "" # string name of the proctype for this instance

    def parse(self, AST):
        AST = clearAst(AST.what) # [ name, proctype name, parameters list]
        self.name = AST[0].what[0]
        self.line = getBestLineNumberForExpresion(AST)
        self.proctype = ast2str(AST[1])

        for x in clearAst(AST[2].what):
            self.params.append(x)

    def __str__(self):
        string = ">> Instance: " + str(self.name)
        string += " @proctype: " + str(self.proctype)
        string += " @line: " + str(self.line)
        string += " @parameters: " + str(self.params)
        return string

################################################################################

class Propertie(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.formula = "" # the formula goes here, everything else in 'params'

    def parse(self, AST):
        AST = AST.what[0]
        self.line = AST.__name__.line
        self.type = Types.propToType[AST.__name__]

        self.formula = AST.what[-1]
        for f in AST.what[:-1:]:
            self.params.append(f)
 
    def __str__(self):
        string = ">> Propertie " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        string += "; and formula " + str(self.formula)
        return string


################################################################################

class Contraint(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self, AST):
        AST = AST.what[0]
        self.type = AST.__name__
        self.line = AST.what[0].__name__.line
        for x in AST.what:
            self.params.append(x)

    def __str__(self):
        string = ">> Contraint: " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters: " + str(self.params)
        return string



################################################################################

class VarDeclaration(ParserBaseElem):
    """ Structure intended to represent a local variable declaration, whose
        scope is the proctype which who it belongs to.
    """
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.domain = [] # values of the domain of the variable
        self.range = []  # start and end of an integer domain
        self.isarray = False # TODO revisar si es necesaria esta variable, de
                             # no serlo borrarla de ParserBaseElem tambien.

    def parse(self, AST):
        self.pypeg = AST
        AST = AST.what # [name, domain]
        self.name = ast2str(AST[0])
        self.line = AST[0].__name__.line
        # get the type and range of the variable
        AST = cleanAst(AST[1::],[],1,True)[0] # clean unicodes of 1st level
        if AST.__name__ == "BOOLEANT":
            self.type = Types.Bool
        elif AST.__name__ == "ENUMT":
            self.type = Types.Symbol
            for x in AST.what:
                if not isinstance(x, unicode):
                    self.domain.append(ast2str(x))
        elif AST.__name__ == "RANGET":
            self.type = Types.Int
            for x in AST.what:
                if not isinstance(x, unicode):
                    self.domain.append(ast2str(x))
            assert(len(self.domain)==2)
        elif AST.__name__ == "ARRAYT":
            self.isarray = True
            self.range.append(ast2str(AST.what[1])) # start
            self.range.append(ast2str(AST.what[3])) # end
            _domain = AST.what[5]
            if _domain.__name__ == "BOOLEANT":
                self.type = Types.BoolArray
            elif _domain.__name__ == "ENUMT":
                self.type = Types.SymbolArray
                for x in _domain.what:
                    if not isinstance(x, unicode):
                        self.domain.append(ast2str(x))
            elif domain.__name__ == "RANGET":
                self.type = Types.IntArray
                for x in domain.what:
                    if not isinstance(x, unicode):
                        self.domain.append(ast2str(x))
            else:
                raise TypeError(domain)
        else:
            raise TypeError(AST.__name__)

    def __str__(self):
        string = ">>> Variable " + str(self.name) + " declaration"
        string += ", of type " + Types.Types[self.type]
        string += ", and domain values: "
        for x in self.domain:
            string += "<" + str(x) + "> "
        return string

################################################################################

class Fault(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre     = None
        self.pos     = []
        self.affects = []

    def parse(self, AST):
        AST = clearAst(AST.what) # [name, pre, pos, type]
        self.line = AST[0].__name__.line
        for x in AST:
            if x.__name__ == "NAME":
                self.name = ast2str(x)
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
                # Clear unicodes and blanks from 1st level to get the effects
                for y in clearAst(x.what):
                    self.affects.append(y)
        if self.pre == None or self.pre == "":
            self.pre = getTrueExpresion()
            self.pre.__name__.file = AST[0].__name__.file
            self.pre.__name__.line = AST[0].__name__.line

    def __str__(self):
        string = ">>> Fault \'" + str(self.name) + "\'"
        string += " @Type: " + str(self.type)
        string += " @Pre: " + str(self.pre)
        string += " @Pos: " + str(self.pos)
        string += " @Affects: " + str(self.affects)
        return string

################################################################################

class Transition(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre = None
        self.pos = []
        self.pc = 0 # program counter number used for compilation

    def parse(self, AST):
        assert(AST.__name__ == "TRANSITION")
        line = str(AST.__name__.line)
        mfile = str(AST.__name__.file)
        self.line = line
        AST = clearAst(AST.what) # [0, name, 0, pre, 0,pos]
        for elem in AST:
            if elem.__name__ == "NAME":
                self.name = ast2str(elem)
            elif elem.__name__ == "EXPRESION":
                self.pre = elem
            elif elem.__name__ == "NEXTLIST":
                for x in clearAst(elem.what):
                    x = clearAst(x.what)
                    nextref = x[0] # a nextref
                    expr = x[1] # an expresion in case of determ asignment, a
                                # range or set in case of nondet asignment.
                    self.pos.append([nextref, expr])
            else:
                raise TypeError(elem.__name__)

        if self.pre == None or self.pre == "":
            self.pre = getTrueExpresion()
            self.pre.__name__.file = mfile
            self.pre.__name__.line = line

    def __str__(self):
        _res = str(self.name) + " -- " + ast2str(self.pre) + " -- "\
             + ast2str(self.pos)
        return _res

#==============================================================================#
# TESTS =======================================================================#
#==============================================================================#

if __name__ == "__main__":
    try:
        print "__Arrancamos__"
        _file = sys.argv[1]
        _file = os.path.join(os.getcwd(), _file)
        debug('debugLBLUE', "original file: " + _file)
        _sys = parse(_file)
        print str(_sys)
    except Error, _e:
        debug("debugRED", str(_e))

    print "__Terminamos__"
#print "Going out at:", str(Debug.lineno())
#exit(0)

# TODO We may need to use shorter names for some methods that are used very
# often, for to enhance readability of the code.
