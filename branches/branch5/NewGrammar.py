from pyPEG import *
import re, fileinput
from Debug import *
import pyPEG



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
    elif isinstance(ast, unicode) or isinstance(ast, str):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += _cl(x)
    elif ast == None:
        pass
    else:
        raise Exception("Not AST type: " + str(ast))

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

def putParenthesis(AST):
    if isinstance(AST, Symbol):
        if len(AST.what) == 3:
            return "(" + putParenthesis(AST.what[0]) + " " + AST.what[1] + " " + putParenthesis(AST.what[2]) + ")"
        elif len(AST.what) == 1:
            return putParenthesis(AST.what[0])
        elif len(AST.what) == 2:
            return AST.what[0] + putParenthesis(AST.what[1])
        else:
            raise TypeError(AST)
    elif isinstance(AST, unicode):
        return AST
    else:
        raise TypeError(AST)
        

################################################################################

def COMMENT():  return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]

# Identifiers
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"


def IDENT():        return [re.compile(identifiers)]
def INT():          return [re.compile(r"\-?\d+")]
def BOOL():         return [re.compile(r"\bFALSE\b|\bTRUE\b")]
def EVENT():        return [(re.compile(r"just\(") \
                           , IDENT, re.compile(r"\)"))
                           ]
def NEXTREF():      return [(IDENT, "'")]


def VALUE():    return [ (re.compile(r"\("), LEVEL5, re.compile(r"\)"))
#                      , INCLUSION
                       , IDENT
                       , INT
                       , BOOL
                       , EVENT
                       , NEXTREF
                       , (re.compile(r"\!"), VALUE)
                       ]

def LEVEL1():    return [ ( VALUE, 0, ( re.compile(r"\*|\/|\%"), LEVEL1)) ]
def LEVEL2():    return [ ( LEVEL1, 0, ( re.compile(r"\+|\-"), LEVEL2)) ]
def LEVEL3():    return [ ( LEVEL2, 0, ( re.compile(r"(?!\=\>)\=|\!\=|\>\=|\<\=|\<|\>"), LEVEL3)) ]
def LEVEL4():    return [ ( LEVEL3, 0, ( re.compile(r"\||\&"), LEVEL4)) ]
def LEVEL5():    return [ ( LEVEL4, 0, ( re.compile(r"\-\>|\<\-\>"), LEVEL5)) ]


def EXPRESION(): return [LEVEL5]


# TESTS ........................................................................
if __name__ == "__main__":

    def TEST(): return EXPRESION

    _file = fileinput.input()
    _ast = parse(TEST, _file, True, COMMENT, packrat = False)
      
    debugGREEN(_ast)

    debugLBLUE(_str(_ast))

    debugRED(putParenthesis(_ast[0]))

