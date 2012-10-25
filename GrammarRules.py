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
import pyPEG
import re, fileinput
from Debug import *
from Utils import _cl, _str, putBrackets
#
#===============================================================================

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

# GRAMMAR is the grammar to parse
def GRAMMAR():   return [SYSTEM] # Brackets so we don't ommit the big Symbol
# And for comments
def COMMENT():  return [re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]


# IDENTIFIERS

reserved = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bPROCTYPE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bENDPROCTYPE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)"

identifiers = reserved + r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"

names = reserved + r"[a-zA-Z_]+\w*"

def NAME():         return [re.compile(names)]
def IDENT():        return [re.compile(identifiers)]
def INT():          return [re.compile(r"\-?\d+")]
def BOOL():         return [re.compile(r"\bFALSE\b|\bTRUE\b")]
def EVENT():        return [(re.compile(r"just\(") \
                           , IDENT, re.compile(r"\)"))
                           ]
def NEXTREF():      return [(IDENT, "'")]

def SET():          return re.compile(r"\{"), 0, ([IDENT, INT, BOOL] \
                           , -1, (re.compile(r"\,") \
                           , [IDENT, INT, BOOL])), re.compile(r"\}")

def RANGE():        return INT, re.compile(r"\.\."), INT

def INCLUSION():    return IDENT, re.compile(r"\bin\b"), [SET, RANGE]


# EXPRESION

def EXPRESION(): return [LEVEL5]

def VALUE():    return [ (re.compile(r"\("), LEVEL5, re.compile(r"\)"))
                       , INCLUSION
                       , NEXTREF
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
def SYSTEM(): return 0, OPTIONS , -1, [ PROCTYPE
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
def PROCTYPE():     return keyword("PROCTYPE"), IDENT, "(", CTXVARS, \
                           SYNCACTS, ")", ":", PROCTYPEBODY, \
                           keyword("ENDPROCTYPE")
def CTXVARS():      return 0, (IDENT, -1, (",", IDENT))
def SYNCACTS():     return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def PROCTYPEBODY(): return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS


def VAR():          return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, re.compile(r"\:"), [ BOOLEAN, SET, RANGE]
def BOOLEAN():      return [keyword("bool")]


def FAULT():        return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return NAME, ":", 0, EXPRESION, \
                           0, ("=>", NEXTEXPR), keyword("is"), [BIZ, STOP, TRANSIENT]
def BIZ():          return keyword("BIZ"), "(", IDENT, -1, (",", IDENT), ")"
def TRANSIENT():    return [keyword("TRANSIENT")]
def STOP():         return [(keyword("STOP"), "(", IDENT, -1, (",", IDENT), ")"), keyword("STOP")]


def INIT():         return keyword("INIT"), 0, EXPRESION

def TRANS():        return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, NAME, "]", ":" \
                            , 0, EXPRESION, 0, ("=>", NEXTEXPR)



# INSTANCES

instparams = [IDENT, INT, BOOL]

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

def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "(", [CTLEXP, LTLEXP], ")"
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "(", [CTLEXP, LTLEXP], ")"
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ";" ,[CTLEXP, LTLEXP], ")"



# CONTRAINTS
def CONTRAINT():    return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(keyword("FAIRNESS"), EXPRESION)]
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", EXPRESION, ",", EXPRESION, ")"



#def MYTEST():   return keyword("HOLA"), "a"


# TESTS ........................................................................
if __name__ == "__main__":

    def TEST(): return GRAMMAR

    _file = fileinput.input()
    _ast = parse(TEST, _file, True, COMMENT, packrat = False)
      
    debugGREEN(_ast)

    debugLBLUE(_str(_ast))

    if len(_ast) and _ast[0].__name__ == EXPRESION:
        debugRED(putBrackets(_ast[0]))

