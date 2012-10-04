#
# En este modulo se determinan las reglas gramaticales que definen el lenguaje
# de entrada para falluto. Las reglas seran interpretadas por la libreria PyPEG.
#===============================================================================


import sys, os, fileinput, re
from pyPEG import keyword, _and, _not, parseLine, parse
from Debug import *



# GRAMMAR is the grammar to parse
def GRAMMAR():   return [SYSTEM] # Brackets so we don't ommit the big Symbol
# And for comments
def COMMENT():  return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]





# IDENTIFIERS ##################################################################
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*"

complexid = r"[a-zA-Z_]+\w*\.[a-zA-Z_]+\w*"



formulasymbols = r""" \+ | \- | \* | \/ | \% |
                      (?!\=\>)\= | \<\= | \>\= | \< | \> | \!\= |
                      \-\> | \<\-\> |
                      \& | \| | \!
                  """

def IDENT():        return re.compile(identifiers)
def COMPLEXID():    return re.compile(complexid)
def INT():          return re.compile(r"\-?\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")
    # Only to be used in properties especification
def EVENT():       return re.compile(r"just\("), COMPLEXID, re.compile(r"\)")
    # for matching ids that don't belong to any formula
def ONLYID():       return [COMPLEXID, IDENT], \
                           _not(re.compile(formulasymbols, re.X))


# OTHERS #######################################################################
def SET():          return "{", 0, ([IDENT, INT], -1, (r",", [IDENT, INT])), "}"
def RANGE():        return INT, "..", INT
def INCLUSION():    return [ ([IDENT, INT], re.compile(r"\bin\b"), SET) \
                           , (INT, re.compile(r"\bin\b"), RANGE) \
                           ]


# MATH FORMULAS ################################################################
def MATH():     return PRODUCT, 0, (re.compile(r"\+|\-"), MATH)
def PRODUCT():  return MATHVAL, 0, (re.compile(r"\*|\/|\%"), PRODUCT)
def MATHVAL():  return [ INT
                       , (re.compile(r"\("), MATH, re.compile(r"\)"))
                       , (re.compile(r"\-"), MATH)
                       , IDENT
                       , COMPLEXID
                       ]


# COMPARISON ###################################################################
def COMPARISON():   return[ (IDENT, re.compile(r"\=|\!\="), ONLYID)
                          , (MATH, re.compile(r"\>|\<|\>\=|\<\=|\=|\!\="), MATH)
                          ]


# PROPOSITIONAL FORMULA ########################################################
def BOOLPROP():     return BOOLCOMP, 0, (re.compile(r"\-\>|\<\-\>"), BOOLPROP) 
def BOOLCOMP():     return BOOLFORM, 0, (re.compile(r"\=|\!\="), BOOLCOMP)
def BOOLFORM():     return BOOLVAL, 0, (re.compile(r"\&|\|"), BOOLFORM)
def BOOLVAL():      return [ (re.compile(r"\("), BOOLPROP, re.compile(r"\)"))
                           , (re.compile(r"\!"), BOOLVAL)
                           , EVENT
                           , INCLUSION
                           , BOOL
                           , COMPARISON
                           , COMPLEXID
                           , IDENT
                           ]


# NEXT EXPRESION ###############################################################
def NEXTEXPR():     return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return IDENT, "'", \
                           [ ( "=", [ ONLYID, BOOLPROP, MATH, NEXTREF]) \
                           , ("in", [ SET, RANGE])
                           ]
def NEXTREF():      return [(IDENT, "'")]




# THE HOLE SYSTEM SPECIFICATION ################################################
def SYSTEM(): return 0, OPTIONS , -1, [ MODULE
                                      , INSTANCE
                                      , SPECIFICATION
                                      , CONTRAINT ]



# OPTIONS ######################################################################
def OPTIONS(): return keyword("OPTIONS"), -1, [ SYSNAME
                                              , CHECKDEADLOCK
                                              , FAULTSYSFAIRDISABLE
                                              , MODULEWFAIRDISABLE ], \
                      keyword("ENDOPTIONS")
                      
def SYSNAME():              return "FLLNAME", re.compile(r"[\w\.\d\_]*")
def CHECKDEADLOCK():        return keyword("CHECK_DEADLOCK")
def FAULTSYSFAIRDISABLE():  return keyword("FAULT_SYS_FAIR_DISABLE")
def MODULEWFAIRDISABLE():   return keyword("MODULE_WEAK_FAIR_DISABLE")




# MODULES ######################################################################
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
def FAULTDECL():    return IDENT, ":", 0, BOOLPROP, \
                           0, ("=>", NEXTEXPR), "is", FAULTTYPE

def MODINIT():      return keyword("INIT"), 0, BOOLPROP

def MODTRANS():     return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":" \
                            , 0, BOOLPROP, 0, ("=>", NEXTEXPR)

def FAULTTYPE():    return [BIZ, STOP, TRANSIENT]
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def TRANSIENT():    return "TRANSIENT"
def STOP():         return [("STOP", "(", IDENT, -1, (",", IDENT), ")"), "STOP"]




# INSTANCES ####################################################################

instparams = [ COMPLEXID, BOOL, INT ]

def INSTANCE():     return keyword("INSTANCE"), IDENT, "=", IDENT \
                           , "(", PARAMLIST, ")"
def PARAMLIST():    return 0, ( instparams, -1, ( ",", instparams))





# SPECIFICATIONS (properties declarations) #####################################

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
                               , BOOLPROP
                               ]


def PROPERTIE():        return [ NORMALBEHAIVIOUR \
                               , FINMANYFAULTS \
                               , FINMANYFAULT \
                               ]
def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "(", CTLEXP, ")"
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "(", CTLEXP, ")"
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ";" ,CTLEXP, ")"





# CONTRAINTS ###################################################################
def CONTRAINT():    return [FAIRNESS, COMPASSION]
def FAIRNESS():     return keyword("FAIRNESS"), BOOLPROP
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", BOOLPROP, ",", BOOLPROP, ")"

















#..........................    TESTING   .......................................

if __name__ == "__main__":

    debugMAGENTA("TESTING...")
    i = 1 
    #Test1
    string = "hola"
    debugYELLOW( "Test1: " + string \
               + " Should match ONLYID and IDENT. Testing...")
    AST, REST = parseLine(string, IDENT, [], True)
    if REST != "":
        debugRED("Test1 NOT passed")
    else:
        debugGREEN("Test1 passed")
    AST, REST = parseLine(string, ONLYID, [], True)
    if REST != "":
        debugRED("Test1 NOT passed")
    else:
        debugGREEN("Test1 passed")
    
    i += 1
    #Test2
    string = "hola.chau"
    debugYELLOW( "Test2: " + string \
               + " Should match ONLYID and COMPLEXID. Testing...")
    AST, REST = parseLine(string, COMPLEXID, [], True)
    if REST != "":
        debugRED("Test2 NOT passed")
    else:
        debugGREEN("Test2 passed")
    AST, REST = parseLine(string, ONLYID, [], True)
    if REST != "":
        debugRED("Test " + str(i) +  " NOT passed")
    else:
        debugGREEN("Test " + str(i) + " passed")


    def EXPRESION():    return [ ONLYID
                               , COMPARISON
                               , MATH
                               , BOOLPROP
                               ]



    debugMAGENTA("If there is a file, test to match its content:")
    _file = fileinput.input()
    _ast  = parse(GRAMMAR, _file, True, COMMENT)

    print "Interpreted:\n\n", _ast

#...............................................................................

