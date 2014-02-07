# Module PreCompiler
# Author Raul
# 31/01/2014 19:38:00

import re
import fileinput
import logging
from pyPEG import parse, Symbol
from GrammarRulesRepair import GRAMMAR
from DebugRepair import debug
from UtilsRepair import getAst, ast2str, commaSeparatedString
from ExceptionsRepair import Error


WARNING = logging.warning
INFO = logging.info
DEBUG = logging.debug

# MODULE PLAIN API #############################################################

def precompile(ast=[], outputFile=""):

    """
        @input ast: parsed model in a pyAST
        @

        * get definitions
        * check there are no cycles in them
        * replace inside definitions ( from leafs to top using dfs)
        * use definitions to replace everywhere else
        * write new file
        * parse it and return the result
    """
    _p = preCompiler(ast)

    _p.sintaxReplacement(outputFile)

    return


# PRECOMPILER CLASS ############################################################

class preCompiler():

    def __init__(self, ast=[]):
        self.ast = ast
        self.defs = {} # Definitions dictionary
        self.adj = {}  # Adjacency dictionary
        self.getDefs()
        self.checkCircularDependance()

    def getDefs(self):
        """ Get the definitions from self.ast and fill in self.defs with them.
        """
        _dlist = getAst(self.ast, ["DEFINE"])
        for _x in _dlist:
            _xn = _x.what[2] # FIXME CACASO
            _xv = _x.what[4] # FIXME CACASO
            self.defs[ast2str(_xn)] = ast2str(_xv)
        DEBUG("Definitions dictionary " + str(self.defs))

    def checkCircularDependance(self):
        """ Check that there is no circular dependance beteween definitions.
            Rise Utils.Error() exception otherwise.
            @ require: must call self.getDefs() first
        """
        self.adj = {}
        for d,v in self.defs.iteritems():
            self.adj[d] = [x for x in v.split() if x in self.defs]
        cycl = hasCycle(self.adj)
        if cycl != []:
            raise Error("Circular dependance in DEFINES: " \
                       + commaSeparatedString(cycl) + ".")

    def sintaxReplacement(self, outputFile=""):
        """ Make the sintax replacements due to DEFINES in the model.

            @return: a string with the model after the sintactic replacements
                     have been done.
        """
        # We need to make replacements in definitions first
        self.setDefs()
        
        replace(self.ast, self.defs, outputFile)

    def setDefs(self):
        """ Make the replacements in self.defs due to defintions it self. """
        visited = {}
        for _d, _dummy in self.defs.iteritems():
            visited[_d] = False
        for _d, _dummy in self.defs.iteritems():
            _dummy, visited = self.setDefsDFS(_d, visited)
    
    def setDefsDFS(self, d, visited):        
        """ A DFS algorithm to set de definitions correctly. """
        if self.adj[d] != []:
            for x in self.adj[d]:
                visited[x] = True
                self.defs[d] = \
                    self.defs[d].replace( x, self.setDefsDFS(x, visited)[0])
        return self.defs[d], visited

# EXTRA FUNCTIONS ##############################################################

# TODO very ineficent algorithm!! make it better
def hasCycle(adj):
    """ Given an adjacency dictionary check if there are cycles in it.

        @input adj: An adjacency dictionary, with names as keys and lists of 
                    dajacent names as values.
        @return: [] if no cycles are found, a list with the first found cycle 
                 otherwise.
    """
    stack = []
    for e,v in adj.iteritems():
        try:
            stack = cycleDFS(e, adj, stack)
        except Exception:
            return stack
    # its acyclic:
    return []

#..............................................................................

def cycleDFS(r, adj, stack):
    for a in adj[r]:
        if a in stack:
            raise Exception(stack)
        else:
            stack.append(a)
        stack = cycleDFS(a, adj, stack)
    return stack[:-1:]

#..............................................................................

def replace(ast=[] , defs={}, path=""):
    """ Write a file with a model from a pyAST structure but making sintax 
        replacements from definitions.

        @input ast: the model in a pyAST.
        @input defs: a dictionary with the sintax replacements to be done.
        @input path: the path to the file to be written.
        @return : a string with the model if path is "". None otherwise.
    """
    result = ""
    if isinstance(ast, Symbol):
        if ast.__name__ == "DEFINE":
            for x in ast.what:
                if isinstance(x, Symbol) and x.__name__ != "EXPRESION":
                    result += ast2str(x)
                else:
                    result += replace(x, defs, "")
        elif ast.__name__ == "OPTIONS" or \
             ast.__name__ == "ENDOPTIONS" or \
             ast.__name__ == "CHECKDEADLOCK" or \
             ast.__name__ == "FAULTFAIRDISABLE" or \
             ast.__name__ == "MODULEWFAIRDISABLE" or \
             ast.__name__ == "COMMENT"or \
             ast.__name__ == "EXPLAIN" or \
             ast.__name__ == "BL":
            result += ast2str(ast)
        else:
            for x in ast.what:
                result += replace(x, defs, "")
    elif isinstance(ast, list):
        for x in ast:
            result += replace(x, defs, "")
    elif isinstance(ast, unicode):
        result += strrepl(ast, defs)
    else:
        raise TypeError()
    if path != "":
        try:
            f = open(path, 'w')
            f.write(result)
        except Exception as e:
            raise Error( "Coudn't write the file with sintax replacement.\n" \
                       + "Because: " + str(e))
        finally:
            f.close()
            result = ""
    return result

#..............................................................................

def strrepl( string="", defs={}):
    """ Return a modified version of a string following sintax definitions.

        @input string; the string we want to modify.
        @input defs: the sintactic definitions for making the replacements
        @return: a string which is equal from 'string' except for the 
                 replacements that 'defs' sugests.
    """
    assert isinstance(string, str) | isinstance(string, unicode) \
           , "The following is not a string: %r" %string
    result = string
    for d, v in defs.iteritems():
#        debug("debugGREEN", "Replacing " + d + " by " + v + " in " + result)
        result = re.sub( u'\\b' + d + u'\\b', v, result)
#        debug("debugLBLUE", "Got " + result)
    return result

# MODULE MAIN ##################################################################


if __name__ == "__main__":

    _file = fileinput.input()

#    logging.basicConfig(filename='logfile.log', level=logging.DEBUG)
#    Logging levels:
#    CRITICAL 50
#    ERROR    40
#    WARNING  30
#    INFO     20
#    DEBUG    10
#    NOTSET   0    
    logging.basicConfig( level=logging.INFO
                       , format = '[    %(levelname)s    ] ' \
                                + '[%(filename)s] %(message)s')

    INFO("Parsing ...")
    _ast = parse(GRAMMAR, _file, False, packrat = False)
    INFO("Parsed <%s>."%_file.filename())
    DEBUG(str(_ast))
    
    INFO("Precompiling <%s> ..."%_file.filename())
    precompile(_ast, _file.filename()+".precompiled")
    INFO("Precompiled into <%s>."%(_file.filename()+".precompiled"))
