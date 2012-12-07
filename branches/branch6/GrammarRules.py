# -*- coding: utf-8 -*-

#===============================================================================
# Modulo GrammarRules.py
# 23 de Octubre del 2012
# Autor: Raul Monti
# F A L L U T O    2 . 0
#
# En este modulo se determinan las reglas gramaticales que definen la 
# sintaxis de entrada para falluto. Las reglas seran interpretadas por
# la libreria PyPEG.
#===============================================================================
#
from pyPEG import *
from pyPEG import _not
import pyPEG
import re, fileinput
from Debug import *
from Utils import _cl, _str, putBrackets
#
#===============================================================================


################################################################################

# GRAMMAR is the grammar to parse
def GRAMMAR():   return [SYSTEM] # Brackets so we don't ommit the big Symbol
# And for comments
def COMMENT():  return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]


# IDENTIFIERS
def RESERVED():     return [re.compile(r"""\barray\b|\bof\b|\bin\b|
                            \bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|
                            \bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|
                            \bCOMPASSION\b|\bU\b|\bV\b|\bS\b|
                            \bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|
                            \bO\b|\bZ\b|\bY\b|\bPROCTYPE\b|\bINSTANCE\b|
                            \bTRANS\b|\bINIT\b|\bVAR\b|\bENDPROCTYPE\b|
                            \bFALSE\b|\bTRUE\b|\bFAULT\b""", re.X)
                           ]

def NAME():         return pyPEG._not(RESERVED), \
                                re.compile(r"[a-zA-Z_]+\w*")
def IDENT():        return pyPEG._not(RESERVED), \
                                re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?")
def INT():          return [re.compile(r"\-?\d+")]
def BOOL():         return [re.compile(r"\bFALSE\b|\bTRUE\b")]
def EVENT():        return [(re.compile(r"just\(") \
                           , IDENT, re.compile(r"\)"))
                           ]
def NEWLINE():      return re.compile('\n')
# el _not en la definición de SUBSCRIPT evita que exista newline entre el 
# nombre del arreglo y el símbolo '[' de la subscripción.
def SUBSCRIPT():    return _not(re.compile(r"""[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?
                                           [ \t\r\f\v]*[\n]""", re.X)) \
                           , IDENT, re.compile(r"\["), [IDENT, INT] \
                           , re.compile(r"\]")

#def SUBSCRIPT():    return pyPEG._not(RESERVED), \
#                           re.compile(r"""[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?
#                                      \[([a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?
#                                      |((-)?\d+))\]""",re.X)

def NEXTREF():      return [([SUBSCRIPT,IDENT], "'")]
def SET():          return re.compile(r"\{"), 0, ([SUBSCRIPT, IDENT, INT, BOOL]\
                           , -1, (re.compile(r"\,") \
                           , [SUBSCRIPT, IDENT, INT, BOOL])), re.compile(r"\}")

def RANGE():        return INT, re.compile(r"\.\."), INT
def INCLUSION():    return [SUBSCRIPT,IDENT], re.compile(r"\bin\b"), [SET,RANGE]



# EXPRESION

def EXPRESION(): return [LEVEL5]

def VALUE():    return [ (re.compile(r"\("), LEVEL5, re.compile(r"\)"))
                       , INCLUSION
                       , NEXTREF
                       , SUBSCRIPT
                       , IDENT
                       , INT
                       , BOOL
                       , EVENT
                       , (re.compile(r"\!"), VALUE)
                       , (re.compile(r"\-"), VALUE)
                       ]

def LEVEL1():   return [ ( VALUE, 0, ( re.compile(r"\*|\/|\%"), LEVEL1)) ]
def LEVEL2():   return [ ( LEVEL1, 0, ( re.compile(r"\+|\-"), LEVEL2)) ]
def LEVEL3():   return [ ( LEVEL2, 0, ( re.compile(r"(?!\=\>)\=|\!\=|\>\=|\<\=|\<|\>"), LEVEL3)) ]
def LEVEL4():   return [ ( LEVEL3, 0, ( re.compile(r"\||\&"), LEVEL4)) ]
def LEVEL5():   return [ ( LEVEL4, 0, ( re.compile(r"\-\>|\<\-\>"), LEVEL5)) ]



def NEXTEXPR():     return NEXTASSIGN, -1, ( ",", NEXTASSIGN)
def NEXTASSIGN():   return NEXTREF, \
                            [ (re.compile(r"\="), EXPRESION)
                            , (re.compile(r"in"), [ SET, RANGE])
                            ]


# SYSTEM SINTAX
def SYSTEM(): return 0, OPTIONS , -1, [ DEFINE
                                      , PROCTYPE
                                      , INSTANCE
                                      , SPECIFICATION
                                      , CONTRAINT ]

# Options
def OPTIONS(): return keyword("OPTIONS"), -1, [ SYSNAME
                                              , CHECKDEADLOCK
                                              , FAULTFAIRDISABLE
                                              , MODULEWFAIRDISABLE ], \
                      keyword("ENDOPTIONS")
                      
def SYSNAME():              return [("SYSNAME", re.compile(r"[\w\.\d\_]*"))]
def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]
def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]
def MODULEWFAIRDISABLE():   return [re.compile(r"INST_WEAK_FAIR_DISABLE")]

# Defines
def DEFINE():       return keyword("DEFINE"), NAME, ":=", EXPRESION

# Proctypes
def PROCTYPE():     return keyword("PROCTYPE"), IDENT, "(", CTXVARS, \
                           SYNCACTS, ")", PROCTYPEBODY, \
                           keyword("ENDPROCTYPE")
def CTXVARS():      return 0, (IDENT, -1, (",", IDENT))
def SYNCACTS():     return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def PROCTYPEBODY(): return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS

def VAR():          return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, re.compile(r"\:"), [BOOLEAN,ENUM,RANGE,ARRAY]
def BOOLEAN():      return [keyword("bool")]
def ENUM():         return re.compile(r"\{"), 0, ([NAME, INT]\
                           , -1, (re.compile(r"\,") \
                           , [NAME, INT])), re.compile(r"\}")
def ARRAY():        return re.compile(r"array"), INT, re.compile(r"\.\."), INT \
                           , re.compile(r"of\b"), [RANGE, BOOLEAN, ENUM]

def FAULT():        return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return NAME, ":", 0, (0, EXPRESION, "=>", 0, NEXTEXPR) \
                           , keyword("is"), [BYZ, STOP, TRANSIENT]
def BYZ():          return keyword("BYZ"), "(", IDENT, -1, (",", IDENT), ")"
def TRANSIENT():    return [keyword("TRANSIENT")]
def STOP():         return [(keyword("STOP"), "(", IDENT, -1 \
                           , (",", IDENT), ")"), keyword("STOP")]

def INIT():         return keyword("INIT"), 0, EXPRESION

def TRANS():        return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, NAME, "]", ":" \
                            , 0, EXPRESION, 0, ("=>", NEXTEXPR)



# INSTANCES

instparams = [SUBSCRIPT, IDENT, INT, BOOL]

def INSTANCE():     return keyword("INSTANCE"), NAME, "=", NAME \
                           , "(", PARAMLIST, ")"
def PARAMLIST():    return 0, ( instparams, -1, ( ",", instparams))




# SPECIFICATIONS (properties declarations)

def SPECIFICATION():    return [ CTLSPEC \
                               , LTLSPEC \
                               , NORMALBEHAIVIOUR \
                               , FINMANYFAULTS \
                               , FINMANYFAULT \
                               ]


# ctl
# TODO agregar las palabras reservadas EG EF etc...
CTLUNOP = r"""
                \! | \bEG\b | \bEX\b | \bEF\b | \bAG\b | \bAX\b | \bAF\b
           """

CTLBINOP = r"""
                \& | \| | \bxor\b | \bxnor\b | \-\> | \<\-\>
           """


def CTLSPEC():          return [(keyword("CTLSPEC"), CTLEXP)]
def CTLEXP():           return [ (CTLVALUE, re.compile(CTLBINOP,re.X), CTLEXP)
                               , (re.compile(r"\bE\b|\bA\b") \
                               , re.compile(r"\[") \
                               , CTLEXP, re.compile(r"\bU\b"), CTLEXP \
                               , re.compile(r"\]"))
                               , CTLVALUE
                               ]
def CTLVALUE():         return [ (re.compile(CTLUNOP,re.X), CTLEXP)
                               , (re.compile(r"\("), CTLEXP, re.compile(r"\)"))
                               , EXPRESION
                               ]


# ltl
ltlbinops = re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
ltluops = re.compile(r"\!|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")

def LTLSPEC():      return [(keyword("LTLSPEC"), LTLEXP)] # , (keyword("LTLSPECNAME"), IDENT, ":=", LTLEXP)]
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , ltlbinops, LTLEXP
def LTLUOP():       return -1 , ltluops, LTLVAL
def LTLVAL():       return [ EXPRESION 
                           , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) 
                           ]



# common properties

def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "->", [CTLEXP, LTLEXP]
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "->", LTLEXP
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ")", "->", LTLEXP



# CONTRAINTS
def CONTRAINT():    return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(keyword("FAIRNESS"), EXPRESION)]
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", EXPRESION, ",", EXPRESION, ")"



#def MYTEST():   return keyword("HOLA"), "a"


# TESTS ........................................................................
if __name__ == "__main__":

    def TEST(): return ARRAY

    _file = fileinput.input()
    _ast = parse(TEST, _file, True, COMMENT, packrat = False)
      
    debugGREEN(_ast)

    debugLBLUE(_str(_ast))

    if len(_ast) and _ast[0].__name__ == EXPRESION:
        debugRED(putBrackets(_ast[0]))

