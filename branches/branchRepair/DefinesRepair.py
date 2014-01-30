# Module DefinesRepair.py
# Author Raul
# Tue 28 Jan 2014 03:14:06 PM ART 

import pyPEG
from pyPEG import Symbol, skip, keyword
import fileinput
from fileinput import *
import re
import DebugRepair
from DebugRepair import *
from ExceptionsRepair import *
from UtilsRepair import *
import UtilsRepair

def DEFINITION(): return keyword(r"DEFINE"), \
                         re.compile(r"[\w]+"), \
                         re.compile(r"[^\r\n]*")
def GRAMMAR():    return -1, [DEFINITION , pyPEG.ignore(r"[^\r\n]*[\r\n]")]
def COMMENT():    return [re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]
def NOREPLACE():  return [re.compile(r"""[\s]*
                                         ( OPTIONS
                                         | CHECK_DEADLOCK
                                         | MODELNAME
                                         | ENDOPTIONS
                                         ).*
                                      """), re.X]
def PROPERTY():   return [ ( re.compile(r"""[\s]*
                                            ( LTLSPEC
                                            | CTLSPEC
                                            | NORMAL_BEHAIVIOUR
                                            | FINITELY_MANY_FAULTS
                                            | FINITELY_MANY_FAULT)[^\"]*"""
                                        ), re.X
                            , 0, STRING
                            , re.compile(r"[\s]*\;.*"))]
def STRING():     return re.compile(r'\"[^\"]*\"')


class Definer():
    """ Class for sintactic definitions replacement during precompiling. """

    def __init__(self):
        self.defs = {}
        self.adj = {}
        self.ast = None
        self.stack = None # for cyclic dependance check

    #--------------------------------------------------------------------------
    def parseDefs(self, path):
        """ Parse de definitions from a file at path using pyPEG and the
            grammar defined above.
            @ input path: the path to the file to parse
            @ return: de pyAST with the definitions
        """
        _f = fileinput.input(path)
        self.ast = pyPEG.parse( GRAMMAR, 
                                fileinput.input(path), 
                                True, 
                                COMMENT, 
                                packrat = False)
        for x in self.ast:
            try:
                _d = self.defs[x.what[0]]
                raise Error( "Define double definition: <" + x.what[0] 
                           + "> at line <" + str(x.__name__.line) + ">.")
            except KeyError:
                self.defs[x.what[0]] = x.what[1]                

    #--------------------------------------------------------------------------
    def checkCircularDependance(self):
        """ Check that there is no circular dependance beteween definitions.
            Rise Utils.Error() exception otherwise.
            @ require: must call parseDefs() first
        """
        # Adjacense dictionary TODO bad english??
        
        self.adj = {}
        for d,v in self.defs.iteritems():
            self.adj[d] = [x for x in v.split() if x in self.defs]
        cycl = self.hasCycleDfs(self.adj)
        if cycl != []:
            raise Error("Circular dependance in DEFINES: " \
                       + commaSeparatedString(cycl) + ".")

    #--------------------------------------------------------------------------
    def hasCycleDfs(self, adj):
        self.stack = []
        self.visited = {}
        for d in adj:
            self.visited[d] = False
        for e,v in self.visited.iteritems():
            if not v:
                try:
                    self.cycleDfs(adj,e)
                except Exception:
                    return self.stack
        # its acyclic:
        return []

    #--------------------------------------------------------------------------
    def cycleDfs(self, adj, r):
        for a in adj[r]:
            if a in self.stack:
                raise Exception(self.stack)
            else:
                self.stack.append(a)
            self.cycleDfs(adj, a)
        self.stack = self.stack[:-1:]


    #--------------------------------------------------------------------------
    def replaceDefs(self, path):
        """ Make a sintactic replacement of definitions in file at path.
            @ input path: path to the file
            @ warning: this method will actualy modify the file if needed
        """
        for d,v in self.defs.iteritems():
            print d, v
        print "................................."
        # First replace inside definitions #TODO use visited flags in algorithm
        for _d in self.adj:
            self.defRepl(_d)

        for d,v in self.defs.iteritems():
            print d, v


        # Replace everywhere except when we have a comment, a definition or 
        # a string
        prog1 = re.compile(r"[\s]*(/\*.*?\*/)?[\s]*DEFINE[^\r\n]*")
        prog2 = re.compile(r"//.*")
        _s = "" # how the new file will look like
        _f = open(path, "r")

        for _l in _f:
            if prog1.match(_l):
                x,y = pyPEG.parseLine(str(_l),DEFINITION,[])
                print _l
                print x
                x = x[0].what
                assert y == ""
                _s += "DEFINE " + UtilsRepair.ss(x[0]) + " " + self.defs[UtilsRepair.ss(x[0])]
            if not (prog1.match(_l) or prog2.match(_l)):
                for _d in self.defs.iteritems():
                    _l = re.subn( u'\\b'+unicode(_d[0])+u'\\b'
                                , unicode(_d[1])
                                , str(_l))[0]
                _s += _l
        debugCURRENT(_s)
        _f = open(path+".aux", 'w')
        _f.write(_s)
        _f.close()

    #--------------------------------------------------------------------------
    def defRepl(self, d):
        """ DFS for definition replacement """
        # if it's leaf
        if self.adj[d] == []:
            return self.defs[d]
        else:
            for x in self.adj[d]:
                ret = self.defRepl(x)
                self.defs[d] = re.subn( u'\\b'+unicode(x)+u'\\b'
                                , unicode(ret)
                                , str(self.defs[d]))[0]
            return self.defs[d]

    #--------------------------------------------------------------------------

    def getReplList(self, line):
        """ From a line of file get, a list of tuples (str,rpl) where 'str'
            is a subsection of the line and 'rpl' indicates if we need to make
            replacements in it or not.
        """
        
        return




class REPL():
    """ Intended to open a file and return a string with it's the file content 
        modified by some replacements, attending to some expetions.

        @input path
        @input rpl
        @input expt
    """
    def __init__( self, path="", rpl={}, expt=[])
        self.canrpl = False
        self.path = path
        self.rpl = rpl
        self.expt = expt
        self.s = ""   # string to place the resulting replaced file.
        self.f = None # the file

    def replace(self):
        """ Make the replacements and return the string """        
        self.f = open(self.path,'r')
        for _l inf self.f:
            while _l != "":
                _r, _l = self.readWhile( _l, NOTALPHA)
                self.s += _r
                if _l != "": 
                    _r, _l = self.readWhile( _l, ALPHA)
                    if _r in self.expt:
                        self.s += _r
                        


    def readWhile(self, line, reg):
        """ Read from line while reg matches. Return whatever read and the
            rest of the line.

            @input line: string from whitch to read
            @input reg: python regular expresion being the condition for reading
        """
        while reg.match(line):
            res = line[0]
            line = line[1:]
        return res, line





if __name__ == "__main__":

    try:
        print "__Arrancamos__"
        _file = sys.argv[1]
        _file = os.path.join(os.getcwd(), _file)
        debug('debugLBLUE', "original file: " + _file)
        D = Definer()
        D.parseDefs(_file)
        D.checkCircularDependance()
        D.replaceDefs(_file)
    except Error, _e:
        debug("debugRED", str(_e))

    print "__Terminamos__"



#TODO hacer los reemplazos sintacticos en las definiciones a medida que se
# verifica la ausencia de dependencia circular. Al hacer el reemplazo sintactico
# en el resto del sistema tirar a la basura los defines ya que no sirven mas.
# En un metodo por separado verificar que no se este queriendo reemplazar algo
# dentro de un string.
