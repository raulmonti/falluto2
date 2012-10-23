#===============================================================================
# Modulo SyntaxRules.py
# 24 de Septiembre del 2012
# Autor: Raul Monti
# F A L L U T O    2 . 0
#
#
# En este modulo se determinan las reglas gramaticales que definen la 
# sintaxis de entrada para falluto. Las reglas seran interpretadas por
# la libreria PyPEG.
#===============================================================================

import re, fileinput
from pyPEG import keyword, parse
from Debug import *


debugTODO("Podria usar MATHFORM en vez de INT para los RANGE. Lo mismo " \
        + "pasa en otro lados.")

debugTODO("Usar CTL en vez de LTL ya que es mucho mas rapido de chequear")


debugTODO("Revisar todo este modulo, packrat por se clava con la ltlspec"  \
           + " G ( just(w) -> X ((just(r) -> X (sys.value = sys.output)) " \
           + "U just(w))).")
debugTODO("Definir todo esto de nuevo, si o si primero en hoja :S")

debugTODO("Lograr trazas de contraejemplo mas cortas y lindas :D")

debugTODO("lo que dice aca abajo")
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


debugTODO("Queremos no determinismo en la declaracion de las nexexpr??")


debugTODO("es Byzantine y NO bizantine :S")


debugTODO("Revisar si NuSMV permite hacer 'entero' in {Symbol1, Symbol2}")

################################################################################
########          ########### ######       #######               ###############
################################# ################## #################### ######



# GRAMMAR is the grammar to parse
def GRAMMAR():   return [SYSTEM] # Brackets so we don't ommit the big Symbol
# And for comments
def COMMENT():  return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]






# Identifiers
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*"

complexid = r"[a-zA-Z_]+\w*\.[a-zA-Z_]+\w*"


def IDENT():        return [re.compile(identifiers)]
def COMPLEXID():    return [re.compile(complexid)]
def INT():          return [re.compile(r"\-?\d+")]
def BOOL():         return [re.compile(r"\bFALSE\b|\bTRUE\b")]
def EVENT():        return [(re.compile(r"just\(") \
                           , COMPLEXID, re.compile(r"\)"))
                           ]

# TODO podria agragar COMPLEXID en el SET
def SET():          return re.compile(r"\{"), 0, ([IDENT, INT, BOOL] \
                           , -1, (re.compile(r"\,") \
                           , [IDENT, INT, BOOL])), re.compile(r"\}")
def RANGE():        return INT, re.compile(r"\.\."), INT


def INCLUSION():    return [IDENT, COMPLEXID], re.compile(r"\bin\b"), [SET, RANGE]
#def INCLUSION():    return [ ([IDENT, INT], re.compile(r"\bin\b"), SET) \
#                           , (INT, re.compile(r"\bin\b"), RANGE) \
#                           ]


# Simple Expressions.
# Operadores anidan a derecha siempre.

BINOP = r""" 
          \<\-\> | \-\> | \<\- |                #logical operators
          \<\= | \>\= | \< | \> | (?!\=\>)\= | \!\= |   #comparison operators
          \+ | \- | \/ | \* | \% |              #math operators
          \& | \|                               #logical operators
         """

UNOP = r""" \! |      #logical not
            \-        #math -
        """

def SIMPLEXPR(): return [ (SIMPVALUE, re.compile(BINOP,re.X), SIMPLEXPR)
                        , SIMPVALUE
                        ]
                        

def SIMPVALUE(): return [ (re.compile(r"\("), SIMPLEXPR, re.compile(r"\)"))
                        , INT
                        , INCLUSION
                        , BOOL
                        , NEXTREF
                        , COMPLEXID
                        , IDENT
                        , EVENT # Should only be used in CONTRAINTS
                        , (re.compile(UNOP,re.X), SIMPLEXPR)
                        ]



# Next expressions
def NEXTEXPR():     return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return IDENT, "'", \
                           [ (re.compile(r"\="), [ SIMPLEXPR, NEXTREF]) \
                           , (re.compile(r"in"), [ SET, RANGE])
                           ]
def NEXTREF():      return [(IDENT, "'")]




# The whole system
def SYSTEM(): return 0, OPTIONS , -1, [ MODULE
                                      , INSTANCE
                                      , SPECIFICATION
                                      , CONTRAINT ]



# Options
def OPTIONS(): return keyword("OPTIONS"), -1, [ SYSNAME
                                              , CHECKDEADLOCK
                                              , FAULTFAIRDISABLE
                                              , MODULEWFAIRDISABLE ], \
                      keyword("ENDOPTIONS")
                      
def SYSNAME():              return [(re.compile(r"FLLNAME"), re.compile(r"[\w\.\d\_]*"))]
def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]
def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]
def MODULEWFAIRDISABLE():   return [re.compile(r"MODULE_WEAK_FAIR_DISABLE")]





# Modules
def MODULE():       return keyword("MODULE"), IDENT, "(", MODCONTVARS, \
                           MODSYNCACTS, ")", ":", MODULEBODY, \
                           keyword("ENDMODULE")

def MODCONTVARS():  return 0, (IDENT, -1, (",", IDENT))
def MODSYNCACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, MODVAR, 0, MODFAULT, 0, MODINIT, 0, MODTRANS

def MODVAR():       return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, ":", [ BOOLEAN, SET, RANGE]
def BOOLEAN():      return [keyword("bool")]

def MODFAULT():     return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return IDENT, ":", 0, SIMPLEXPR, \
                           0, ("=>", NEXTEXPR), "is", [BIZ, STOP, TRANSIENT]

def MODINIT():      return keyword("INIT"), 0, SIMPLEXPR

def MODTRANS():     return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":" \
                            , 0, SIMPLEXPR, 0, ("=>", NEXTEXPR)
#def FAULTTYPE():    return [BIZ, STOP, TRANSIENT]
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def TRANSIENT():    return ["TRANSIENT"]
def STOP():         return [("STOP", "(", IDENT, -1, (",", IDENT), ")"), "STOP"]








# INSTANCES

    # we need complexid, int and bool for context variables, and ident for
    # synchronous actions
instparams = [COMPLEXID, IDENT, INT, BOOL]

def INSTANCE():     return keyword("INSTANCE"), IDENT, "=", IDENT \
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
                               , SIMPLEXPR
                               ]


# ltl
ltlbinops = re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
ltluops = re.compile(r"\!|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")

def LTLSPEC():      return [(keyword("LTLSPEC"), LTLEXP)] # , (keyword("LTLSPECNAME"), IDENT, ":=", LTLEXP)]
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , ltlbinops, LTLEXP
def LTLUOP():       return -1 , ltluops, LTLVAL
def LTLVAL():       return [ SIMPLEXPR 
                           , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) 
                           ]



# common properties

def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "(", [CTLEXP, LTLEXP], ")"
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "(", [CTLEXP, LTLEXP], ")"
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ";" ,[CTLEXP, LTLEXP], ")"



# CONTRAINTS
def CONTRAINT():    return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(keyword("FAIRNESS"), SIMPLEXPR)]
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", SIMPLEXPR, ",", SIMPLEXPR, ")"





# SEMANTICS ....................................................................

# Maths
def MATHEXP():  return PRODUCT, 0, (re.compile(r"\+|\-"), MATHEXP)
def PRODUCT():  return MATHVAL, 0, (re.compile(r"\*|\/|\%"), PRODUCT)
def MATHVAL():  return [ INT
                       , (re.compile(r"\("), MATHEXP, re.compile(r"\)"))
                       , (re.compile(r"\-"), MATHEXP)
                       , NEXTREF
                       , IDENT
                       , COMPLEXID
                       ]


# Booleans
def COMPARISON():   return (MATHEXP, re.compile(r"\>|\<|\>\=|\<\=|\=|\!\="), MATHEXP)

def BOOLEXP():      return BOOLCOMP, 0, (re.compile(r"\-\>|\<\-\>"), BOOLEXP) 
def BOOLCOMP():     return BOOLFORM, 0, (re.compile(r"\=|\!\="), BOOLCOMP)
def BOOLFORM():     return BOOLVAL, 0, (re.compile(r"\&|\|"), BOOLFORM)
def BOOLVAL():      return [ (re.compile(r"\("), BOOLEXP, re.compile(r"\)"))
                           , (re.compile(r"\!"), BOOLVAL)
                           , EVENT
                           , INCLUSION
                           , BOOL
                           , COMPARISON
                           , NEXTREF
                           , COMPLEXID
                           , IDENT
                           ]

def SYMBCOMPARISON(): return ( [IDENT, COMPLEXID]
                            , re.compile(r"\=|\!\=")
                            , [IDENT, COMPLEXID]
                            )


# TESTS ........................................................................
if __name__ == "__main__":

    def TEST(): return GRAMMAR

    _file = fileinput.input()
    _ast = parse(TEST, _file, True, packrat = True)
    
    debugGREEN(_ast)


