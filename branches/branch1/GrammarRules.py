#===============================================================================
# Modulo GrammarRules.py
# 22 de Septiembre del 2012
# Autor: Raul Monti
# F A L L U T O    2 . 0
#
#
# En este modulo se determinan las reglas gramaticales que definen la 
# gramatica de entrada para falluto. Las reglas seran interpretadas por
# la libreria PyPEG.
#===============================================================================

import re
from pyPEG import keyword
from Debug import *


debugTODO("Podria usar MATHFORM en vez de INT para los RANGE. Lo mismo " \
        + "pasa en otro lados.")

debugURGENT("Usar CTL en vez de LTL ya que es mucho mas rapido de chequear")


debugTODO("Revisar todo este modulo, packrat por se clava con la ltlspec"  \
           + " G ( just(w) -> X ((just(r) -> X (sys.value = sys.output)) " \
           + "U just(w))).")
debugTODO("Definir todo esto de nuevo, si o si primero en hoja :S")

debugTODO("Lograr trazas de contraejemplo mas cortas y lindas :D")

debugURGENT("lo que dice aca abajo")
"""
    Notar que en la regla de NEXTASIGN, IDENT nunca va a matchear porque 
    PROPFORM contiene a los matches de IDENT, y por lo tanto matchea antes. Sin 
    embargo no quiere decir que el valor devuelto sea un formula proposicional 
    (puede ser por ejemplo una variable que represente un valor entero y no un 
    booleano).
    Me parece que es un error en lo que estoy definiendo. No deberia definir
    las cosas en base a significados semanticos como "formula proposional porque
    es un valor booleano". Sin embargo hacerlo ayuda muchisimo a no tener que
    revisar todo mas adelante.
"""



################################################################################
########          ########### ######       #######               ###############
################################# ################## #################### ######



# GRAMMAR is the grammar to parse
def GRAMMAR():      return [SYSTEM] # Brackets so we don't ommit the big Symbol
# And for comments
def COMMENT():  return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]






# Identifiers
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*"

complexid = r"[a-zA-Z_]+\w*\.[a-zA-Z_]+\w*"


def IDENT():        return re.compile(identifiers)
def COMPLEXID():    return re.compile(complexid)
def INT():          return re.compile(r"\-?\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")
def EVENT():       return "just(", COMPLEXID, ")"

# TODO podria agragar COMPLEXID en el SET
def SET():          return "{", 0, ([IDENT, INT], -1, (r",", [IDENT, INT])), "}"
def RANGE():        return INT, "..", INT


def INCLUSION():    return [ ([IDENT, INT], re.compile(r"\bin\b"), SET) \
                           , (INT, re.compile(r"\bin\b"), RANGE) \
                           ]


# Simple Expressions.
# Operadores anidan a derecha siempre.

BINOP = r""" 
          \<\-\> | \-\> | \<\- |                #logical operators
          \<\= | \>\= | \< | \> | \= | \!\= |   #comparison operators
          \+ | \- | \/ | \* | \% |              #math operators
          \& | \|                               #logical operators
         """

UNOP = r""" \! |      #logical not
            \-        #math -
        """

def SIMPLEXPR(): return [ \
                          (SIMPVALUE, re.compile(BINOP,re.X), SIMPLEXPR)
                        , (re.compile(UNOP,re.X), SIMPLEXPR)
                        , (re.compile(r"\("), SIMPLEXPR, re.compile(r"\)"))
                        , SIMPVALUE
                        ]
                        

def SIMPVALUE(): return [ INT
                        , INCLUSION
                        , BOOL
                        , COMPLEXID
                        , IDENT
                        , EVENT # Should only be used in CONTRAINTS
                        ]



# Next expressions
def NEXTEXPR():     return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return IDENT, "'", \
                           [ ( "=", [ SIMPLEXPR, NEXTREF]) \
                           , ("in", [ SET, RANGE])
                           ]
def NEXTREF():      return IDENT, "'"






# The whole system
def SYSTEM(): return 0, OPTIONS , -1, [ MODULE
                                      , INSTANCE
                                      , SPECIFICATION
                                      , CONTRAINT ]






# Options
def OPTIONS(): return keyword("OPTIONS"), -1, [ SYSNAME
                                              , CHECKDEADLOCK
                                              , FAULTSYSFAIRDISABLE
                                              , MODULEWFAIRDISABLE ], \
                      keyword("ENDOPTIONS")
                      
def SYSNAME():              return "FLLNAME", re.compile(r"[\w\.\d\_]*")
def CHECKDEADLOCK():        return keyword("CHECK_DEADLOCK")
def FAULTSYSFAIRDISABLE():  return keyword("FAULT_SYS_FAIR_DISABLE")
def MODULEWFAIRDISABLE():   return keyword("MODULE_WEAK_FAIR_DISABLE")





# Modules
def MODULE():       return keyword("MODULE"), IDENT, "(", MODCONTVARS, \
                           MODSYNCACTS, ")", ":", MODULEBODY, \
                           keyword("ENDMODULE")

def MODCONTVARS():  return 0, (IDENT, -1, (",", IDENT))
def MODSYNCACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, MODVAR, 0, MODFAULT, 0, MODINIT, 0, MODTRANS

def MODVAR():       return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, ":", [ BOOLEAN, SET, RANGE]
def BOOLEAN():      return keyword("bool")

def MODFAULT():     return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return IDENT, ":", 0, SIMPLEXPR, \
                           0, ("=>", NEXTEXPR), "is", FAULTTYPE

def MODINIT():      return keyword("INIT"), 0, SIMPLEXPR

def MODTRANS():     return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":" \
                            , 0, SIMPLEXPR, 0, ("=>", NEXTEXPR)
def FAULTTYPE():    return [BIZ, STOP, TRANSIENT]
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def TRANSIENT():    return "TRANSIENT"
def STOP():         return [("STOP", "(", IDENT, -1, (",", IDENT), ")"), "STOP"]








# Instances

instparams = COMPLEXID

def INSTANCE():     return keyword("INSTANCE"), IDENT, "=", IDENT \
                           , "(", PARAMLIST, ")"
def PARAMLIST():    return 0, ( instparams, -1, ( ",", instparams))







# Specifications (properties declarations)

CTLUNOP = r"""
                \! | \bEG\b | \bEX\b | \bEF\b | \bAG\b | \bAX\b | \bAF\b
           """

CTLBINOP = r"""
                \& | \| | \bxor\b | \bxnor\b | \-\> | \<\-\>
           """


def SPECIFICATION():    return [CTLSPEC, PROPERTIE]

def CTLSPEC():          return keyword("CTLSPEC"), CTLEXP
def CTLEXP():           return [ (CTLVALUE, re.compile(CTLBINOP,re.X), CTLEXP)
                               , (re.compile(r"\bE\b|\bA\b") \
                               , re.compile(r"\[") \
                               , CTLEXP, re.compile(r"\bU\b"), CTLEXP \
                               , re.compile(r"\]"))
                               , CTLVALUE
                               ]
def CTLVALUE():         return [ (re.compile(CTLUNOP,re.X), CTLEXP)
                               , (re.compile(r"\("), CTLEXP, re.compile(r"\)"))
                               , SIMPLEXPR
                               ]


def PROPERTIE():        return [ NORMALBEHAIVIOUR \
                               , FINMANYFAULTS \
                               , FINMANYFAULT \
                               ]
def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "(", CTLEXP, ")"
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "(", CTLEXP, ")"
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ";" ,CTLEXP, ")"
#def NGOODTRANS():       return keyword("N_GOOD_TRANS") \
#                               , "(", INT, ";", CTLEXP, ")"





# Contraints
def CONTRAINT():    return [FAIRNESS, COMPASSION]
def FAIRNESS():     return keyword("FAIRNESS"), SIMPLEXPR
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", SIMPLEXPR, ",", SIMPLEXPR, ")"








