from pyPEG import *
import re, fileinput
from Debug import *


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


