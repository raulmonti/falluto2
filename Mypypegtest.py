"""
    En esta gramatica logro resolver el problema que tenia en otras, en las
    cuales Identificadores solitarios eran parseados como formulas 
    proposicionales o matematicas, cuando en realidad no se sabe lo que son
    hasta mas adelante, en el chequeo semantico.
    Solo dejo aca como ejemplo las formulas matematicas que en este caso no
    matechean IDENT's solitarios (identificadores no precedidos ni sucedidos 
    por algun operador matematico)
"""




import sys, os, fileinput, re
from pyPEG import keyword, _and, _not, parse


# Identifiers
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*"

complexid = r"[a-zA-Z_]+\w*\.[a-zA-Z_]+\w*"


def IDENT():        return re.compile(identifiers)
def COMPLEXID():    return re.compile(complexid)
def INT():          return re.compile(r"\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")



# Math
FLMO = r"\-"

SLMO = r"\*|\/|\%"

TLMO = r"\+|\-"

SYMBOLS = TLMO + "|" + SLMO + "|" + FLMO + "|"



def ONLYID():   return IDENT, _nor(re.compile(SYMBOLS))

def MATH():     return _not(ONLYID), SUM()

def SUM():      return PROD, 0, (re.compile(TLMO), SUM)

def PROD():     return MATHVAL, 0, (re.compile(SLMO), PROD)

def MATHVAL():  return [ IDENT
                      , INT
                      , (re.compile(r"\("), SUM, re.compile(r"\)"))
                      , (re.compile(FLMO), SUM)
                      ]


def SIMPLEXP(): return [ MATH, IDENT ]




if __name__ == "__main__":

    _file = fileinput.input()
    _ast  = parse(SIMPLEXP, _file, True)

    print "Interpreted:\n\n", _ast
