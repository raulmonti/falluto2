import sys, os, fileinput
from pyPEG import *
 


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

def SET():          return "{", 0, ([IDENT, INT], -1, (r",", [IDENT, INT])), "}"
def RANGE():        return INT, "..", INT

def INCLUSION():    return [ ([IDENT, INT], re.compile(r"\bin\b"), SET) \
                           , (INT, re.compile(r"\bin\b"), RANGE) \
                           ]




# Math
FLMO = r"\-"

SLMO = r"\*|\/|\%"

TLMO = r"\+|\-"

def MATH(): return SUM

def SUM(): return PROD, 0, (re.compile(TLMO), SUM)

def PROD(): return MATHVAL, 0, (re.compile(SLMO), PROD)

def MATHVAL(): return [ COMPLEXID
                      , INT
                      , IDENT
                      , (re.compile(r"\("), SUM, re.compile(r"\)"))
                      , (re.compile(FLMO), SUM)
                      ]



GLBO = r"\-\>|\<\-\>" #Grater level operators (lower presedence)

TLBO = r"\||\&" 

SLBO = r"\=|\!\="

FLBO = r"\!"

MCOMPOP = r"\>|\<|\<\=|\>\=|\!\=|\=" # Operators for math comparison


def BOOLPROP(): return BOOLFORM, 0, (re.compile(GLBO), BOOLPROP)

def BOOLFORM(): return BOOLCOMP, 0, (re.compile(TLBO), BOOLFORM)

def BOOLCOMP(): return BOOLVAL, 0, (re.compile(SLBO), BOOLCOMP)

def BOOLVAL(): return [ BOOL
                      , (MATH, re.compile(MCOMPOP), MATH)
                      , (re.compile(r"\("), BOOLPROP, re.compile(r"\)"))
                      , (re.compile(FLBO), BOOLPROP)
                      , INCLUSION
                      , IDENT
                      ]



def SIMPLEXP(): return [MATH, BOOLPROP]



if __name__ == "__main__":

    _file = fileinput.input()
    _ast  = parse(MATH, _file, True)

    print "Interpreted:\n\n", _ast




    
