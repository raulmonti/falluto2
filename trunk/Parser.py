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
from Utils import cleanAst, ast2str, getBestLineNumberForExpresion, getAst, rmw
from Utils import clearAst, ast2lst, getAst2
import Utils
import shutil
import os.path
import sys
import os

#==============================================================================#
# MODULE PLAIN API ============================================================#
#==============================================================================#

def parse(filePath = None):
    """ Use PyPEG to parse de file into a PyPEG structure. Use this structure
        to fill up our specific structures which are easier to work with.
        Returns a 'Model' instance with the parsed model.
        
        @input filePath: the path of the file to be parsed.
    """
    if filePath == None or not os.path.isfile(filePath):
        raise Error( "Path <"+ str(filePath) +"> is not a valid file to "\
                   + "parse :S.")
    try:
        _f = open(filePath, 'a')
        _f.write("//Line to avoid problems with pyPEG line count.")
        _f.close()
        # packrat = True seems to be brocken :S TODO check if it is
        LDEBUG("Parsing with pyPEG...")
        _ast = pyPEG.parse(GRAMMAR, 
                           fileinput.input(filePath), 
                           False, 
                           COMMENT, 
                           packrat = False)
    except Exception, _e:
        raise Error(str(_e))
    # get everything inside our Model structure:
    _res = Model()
    _res.parse(_ast[0])
    return _res


# Auxiliary functions =========================================================#

def getTrueExpresion():
    string = u'True'
    ast = pyPEG.parseLine(string, EXPRESION,[],True,COMMENT)
    return ast[0][0]


#==============================================================================#


class ParserBaseElem(object):
    """ Class to be enheritate when representing a parsed element. """

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
            lst = ast2lst(self.pypeg)
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

#==============================================================================#

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
        self.nnnprops   = 0     #Number of no named properties

    def getProperties(self):
        """ get the parsed properties in a dictionary with property names
            as keys and property objects as values.
        """
        return self.properties

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
        assert ast.__name__ == 'MODEL'
        self.clear()
        self.pypeg = ast
        for elem in clearAst(ast.what):
            if elem.__name__ == "OPTIONS":
                # get each option
                _opts = getAst(elem,['OPT'])
                for opt in _opts:
                    opt = opt.what[0]
                    o = Option()
                    o.parse(opt)
                    if o.type == Types.Modname:
                        self.name = ast2str(getAst2(opt, ['MNAME']))
                    if o.name in self.options:
                        WARNING( "Redeclared option \'" + o.name \
                               + "\', using only the last declaration.\n")
                    LDEBUG("New Option: " + o.name)
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
                if p.name == "":
                    p.name = "NN#property#" + str(self.nnnprops)
                    self.nnnprops += 1
                elif p.name in self.properties:
                    raise Error("You have more than one propertie named '"
                               + p.name + "'.")
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

#==============================================================================#

class Option(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)

    def parse(self, ast):
        self.pypeg = ast
        self.name = ast.__name__
        self.line = ast.__name__.line
        if ast.__name__ == "MODULEWFAIRDISABLE":
            self.type = Types.WFDisable
        elif ast.__name__ == "FAULTFAIRDISABLE":
            self.type = Types.FFDisable
        elif ast.__name__ == "CHECKDEADLOCK":
            self.type = Types.Checkdk
        elif ast.__name__ == "MODNAME":
            self.type = Types.Modname
        else:
            LWARNING("Bad option " + str(ast.__name__))

    def __str__(self):
        string = ">> Option " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        return string

#==============================================================================#

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

#==============================================================================#

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
        self.pypeg = AST
        AST = clearAst(AST.what) # [ name, context vars, synchro acts, body ]
        self.name = ast2str(AST[0])
        self.line = AST[0].__name__.line
        # get the context variables indentifiers
        for cv in getAst(getAst(AST,["CTXVARS"])[0],["NAME"]):
            self.contextvars.append(ast2str(cv))
        # get the synchronization identifiers
        for sa in getAst(getAst(AST,["SYNCACTS"])[0],["NAME"]):
            self.synchroacts.append(ast2str(sa))
        # get the body of the prctype
        AST = getAst(AST,["PROCTYPEBODY"])[0]
        for elem in clearAst(AST.what):
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
                    self.init = rmw(getAst(elem,['EXPRESION'])[0])
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


#==============================================================================#

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

#==============================================================================#

class Propertie(ParserBaseElem):

    numNnPropertie = 0 # number of no named properties

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.formula = "" # the formula goes here
        self.explain = "" # the explanation goes here
                          # everything else except the name goes in params
        self.actions = [] # for ENSURE and ATMOST meta-properties
        self.limit = -1   # for ENSURE and ATMOST meta-properties

    def parse(self, ast):
        self.pypeg = ast
        self.line = ast.__name__.line
        self.name = ast2str(getAst2(ast,['PROPNAME']))
        self.explain = ast2str(getAst2(ast,['EXPLAIN']))
        ast = clearAst(ast.what)
        #After cleaning we should get the name, the property and the explanation
        for y in ast:
            if y.__name__ != "EXPLAIN" and y.__name__ != 'PROPNAME':
                y = rmw(y)
                self.type = Types.propToType[y.__name__]
                y = clearAst(y.what)
                for x in y:
                    if x.__name__ == 'CTLEXP' or x.__name__ == 'LTLEXP':
                        self.formula = x
                    elif x.__name__ == 'ANAME':
                        self.actions.append(x)
                    elif x.__name__ == 'LIMIT':
                        self.limit = x
                    elif x.__name__ == 'FNAME':
                        self.params.append(x)
                    else:
                        assert False
 
    def __str__(self):
        string = ">> Propertie " + str(self.name)
        string += ", of type " + str(self.type)
        string += ", at line " + str(self.line)
        string += "; with parameters " + str(self.params)
        string += "; and formula " + str(self.formula)
        return string


#==============================================================================#

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



#==============================================================================#

class VarDeclaration(ParserBaseElem):
    """ Structure intended to represent a local variable declaration, whose
        scope is the proctype which who it belongs to.
    """
    def __init__(self):
        ParserBaseElem.__init__(self)
        self.type = None

    class VarType():
        def __init__(self, t=None, s=None, e=None, d=None):
            self.type = t    # From Type module.
            self.start = s   # For array types.
            self.end = e     # For array types.
            self.domain = d  # The values of the domain in case of enum or 
                             # range. Would be another VarType instance in
                             # case of arrays.
        def __str__(self):
            string = ""
            if self.type == Types.Array:
                string += 'array '
                string += str(self.start) + '..' + str(self.end) + ' of '
                string += str(self.domain)
            elif self.type == Types.Int:
                string += 'Range ' + str(self.domain[0])\
                        + '..' + str(self.domain[1])
            elif self.type == Types.Bool:
                string += 'Boolean'
            elif self.type == Types.Symbol:
                string += 'Symbol'
                if self.domain != None:
                    string += ' {'
                    for x in self.domain[:-1:]:
                        string += str(x) + ', '
                    string += str(self.domain[-1]) + '}'
            else:
                assert False
            return string

    def parse(self, AST):
        self.pypeg = AST
        AST = AST.what
        self.name = ast2str(AST[0])
        self.line = AST[0].__name__.line
        # get the type and range of the variable
        AST = clearAst(AST)[1] # [name, domain][1] = domain
        self.type = self.parseTypeRec(AST)

    def parseTypeRec(self, ast):
        """ ast needs to be a Symbol defining the type of the variable """
        assert isinstance(ast, Symbol)
        _type = self.VarType()
        # get the type
        ast = ast.what[0]
        _name = ast.__name__
        ast = clearAst(ast.what)
        if _name == "ARRAYT":
            _type.type = Types.Array
            _type.start = ast2str(ast[0])
            _type.end = ast2str(ast[1])
            _type.domain = self.parseTypeRec(ast[2])
        elif _name == "BOOLEANT":
            _type.type = Types.Bool
        elif _name == "ENUMT":
            _type.type = Types.Symbol
            _type.domain = []
            for x in ast:
                _type.domain.append(ast2str(x))
        elif _name == "RANGET":
            _type.type = Types.Int
            _type.domain = []
            for x in ast:
                _type.domain.append(ast2str(x))
            assert(len(_type.domain)==2)
        else:
            raise TypeError(_name)
        return _type

    def __str__(self):
        string = ">>> Variable " + str(self.name) + " declaration"
        string += ", of type: "
        string += str(self.type)
        return string

#==============================================================================#

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
                self.pre = rmw(x)
            elif x.__name__ == "NEXTLIST":
                for elem in x.what:
                    elem = rmw(elem.what)
                    nextref = clearAst(elem[0].what[0])
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

#==============================================================================#

class Transition(ParserBaseElem):

    def __init__(self):
        ParserBaseElem.__init__(self)
        self.pre = None
        self.pos = []
        self.pc = 0 # program counter number used for compilation

    def parse(self, AST):
        assert(AST.__name__ == 'TRANSITION')
        self.pypeg = AST
        line = str(AST.__name__.line)
        mfile = str(AST.__name__.file)
        self.line = line
        AST = clearAst(AST.what) # [0, name, 0, pre, 0,pos]
        for elem in AST:
            if elem.__name__ == "NAME":
                self.name = ast2str(elem)
            elif elem.__name__ == "PRE":
                self.pre = rmw(elem.what[0])
            elif elem.__name__ == "POS":
                for x in clearAst(elem.what[0].what):
                    x = clearAst(x.what)
                    nextref = x[0].what[0] # a nextref
                    expr = rmw(x[1]) # an expresion in case of determ asignment,
                                     # a range or set in case of nondet
                                     # asignment.
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
