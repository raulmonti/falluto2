# Module PreCompiler
# Author Raul
# 31/01/2014 19:38:00

import fileinput
from pyPEG import parse
from GrammarRulesRepair import GRAMMAR
from DebugRepair import debug
from UtilsRepair import getAst, ast2str, commaSeparatedString
from ExceptionsRepair import Error

# MODULE PLAIN API #############################################################

def precompile(ast=[]):

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

    _p.sintaxReplacement()

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
        debug("debugGREEN", "Definitions dictionary " + str(self.defs))

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

    def sintaxReplacement(self):
        """ Make the sintax replacements due to DEFINES in the model.

            @return: a string with the model after the sintactic replacements
                     have been done.
        """
        # We need to make replacements in definitions first
        self.setDefs()
        
        replace(self.ast, self.defs)



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


def cycleDFS(r, adj, stack):
    for a in adj[r]:
        if a in stack:
            raise Exception(stack)
        else:
            stack.append(a)
        stack = cycleDFS(a, adj, stack)
    return stack[:-1:]


def replace(ast=[],defs={}):
    """ Replace defs in the model in ast. """
    if:
    elif:
    else
        raise TypeError()
    return


# MODULE MAIN ##################################################################


if __name__ == "__main__":

    _file = fileinput.input()

    print "Parsing ...."

    _ast = parse(GRAMMAR, _file, False, packrat = False)

    debug("debugGREEN", _ast)

    print "Precompiling ...."

    precompile(_ast)


