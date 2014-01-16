# -*- coding: utf-8 -*-


#===============================================================================
# Modulo GrammarRules.py
# 24 de Octubre del 2013
# Autor: Raul Monti
# F A L L U T O    2 . 0
#
# En este modulo se determinan las reglas sintacticas del lenguaje de 
# falluto2.0. Las reglas seran interpretadas por la libreria PyPEG.
#
# Ejemplo de código aceptado:
#
#
#- OPTIONS
#- 
#- ENDOPTIONS
#-
#-
#- PROCTYPE proc1(var1, act1):
#-
#-
#-
#- ENDPROCTYPE
#- 
#-
#-
#- INSTANCE inst1 = proc1( False, synchro)
#-
#-
#-
#-
#-
#-
#-
#-
#-
#-
#
#
#===============================================================================
#
from pyPEG import *
from pyPEG import _not
import pyPEG
import re, fileinput
from DebugRepair import *
from Utils import _cl, _str, putBrackets
#
#===============================================================================


# TODO Notar que no estoy verificando solo sintaxis aca --->> eso esta muy mal
# Asegurarse de que solo se revise la estructura sintáctica, y no la
# semantica ni nada por el estilo.

# TODO Everything should be in english (or everyone will hate me). I'm proud
# of my beautiful language though.

################################################################################

def GRAMMAR():
    """ This is the grammar rule to parse for Falluto2.0.
    """
    return [SYSTEM] # Brackets so we don't ommit the big Symbol

#..............................................................................
def COMMENT():
    """ Comments syntax for Falluto2.0., just as in C :D.
    """
    return [re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]


# IDENTIFIERS #################################################################
def RESERVED():
    """ Reserved names with specific uses, not to be used as user variable 
        names.
    """
    return [re.compile( r"""

                        # Global options
                        \bOPTIONS\b|\bENDOPTIONS\b|\bCHECKDEADLOCK\b|
                        \bMODELNAME\b|

                        # Fairness and LTL                        
                        \bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|
                        \bT\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|

                        # CTL
                        \bAX\b|\bEX\b|\bAF\b|\bEF\b|\bAG\b|\bEG\b|

                        # Proctypes
                        \bPROCTYPE\b|\bINSTANCE\b|\bTRANS\b|\bINIT\b|
                        \bVAR\b|\bFAULT\b|\bENDPROCTYPE\b| 

                        # Math
                        \bxor\b|\bxnor\b|\bFalse\b|\bTrue\b|

                        # Others
                        \bin\b|\bjust\b|\bis\b|\barray\b|\bof\b

                        """, re.X)]

#..............................................................................
def NAME(): return pyPEG._not(RESERVED), re.compile(r"[a-zA-Z_]+\w*")

#..............................................................................
def IDENT():
    """ Name construction used to identify diferent kind of variables and 
        actions from any instance or proctype. The '.' represents 'belonging', 
        for example 'instance.variable' would identify the variable named 
        'variable' from the instance named 'instance'.
    """
    return pyPEG._not(RESERVED), re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?")

#..............................................................................
def INT(): return [re.compile(r"\-?\d+")]

#..............................................................................
def BOOL(): return [re.compile(r"\bFalse\b|\bTrue\b")]

#..............................................................................
def EVENT(): return [(re.compile(r"just\(") , IDENT, re.compile(r"\)"))]

#..............................................................................
def NEWLINE(): return re.compile('\n')

#..............................................................................
def SUBSCRIPT():
    """ List subscripts, to access its elements. Subscripts opening bracket
        should be just after the list name, no white spaces would be tolerated
        beteween the list name and the opening bracket.
    """
    return pyPEG._not(re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?\s+")),\
           IDENT, re.compile(r"\["), [IDENT, INT], re.compile(r"\]")

#..............................................................................
def NEXTREF():
    """ A reference to the value of a variable in the next state.
    """
    return [([SUBSCRIPT,IDENT], "'")]

#..............................................................................
def SET(): return re.compile(r"\{"), 0, ([SUBSCRIPT, IDENT, INT, BOOL]\
               , -1, (re.compile(r"\,") \
               , [SUBSCRIPT, IDENT, INT, BOOL])), re.compile(r"\}")

#..............................................................................
def RANGE(): return INT, re.compile(r"\.\."), INT

#..............................................................................
def INCLUSION(): return [SUBSCRIPT,IDENT], re.compile(r"\bin\b"), [SET,RANGE]



# EXPRESION ###################################################################

def EXPRESION(): return [PROP]

#..............................................................................
def VALUE():    return [ (re.compile(r"\("), PROP, re.compile(r"\)"))
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

#..............................................................................
def PROD():     return [ ( VALUE, 0, ( re.compile(r"\*|\/|\%"), PROD)) ]

#..............................................................................
def SUM():      return [ ( PROD, 0, ( re.compile(r"\+|\-"), SUM)) ]

#..............................................................................
def COMP():     return [ ( SUM, 0, 
                         ( re.compile(r"(?!\=\>)\=|\!\=|\>\=|\<\=|\<|\>"), COMP)
                         ) 
                       ]

#..............................................................................
def LOGIC():    return [ ( COMP, 0, ( re.compile(r"\||\&"), LOGIC)) ]

#..............................................................................
def PROP():     return [ ( LOGIC, 0, ( re.compile(r"\-\>|\<\-\>"), PROP)) ]

#..............................................................................
def NEXTLIST():     return NEXTASSIGN, -1, ( ",", NEXTASSIGN)

#..............................................................................
def NEXTASSIGN():   return NEXTREF, \
                            [ (re.compile(r"\="), EXPRESION)
                            , (re.compile(r"in"), [ SET, RANGE])
                            ]


# SYSTEM SINTAX ---------------------------------------------------------------
def SYSTEM(): return 0, OPTIONS , -1, [ DEFINE
                                      , PROCTYPE
                                      , INSTANCE
                                      , PROPERTY
                                      , CONSTRAINT ]

# OPTIONS ---------------------------------------------------------------------
def OPTIONS(): return keyword("OPTIONS"), -1, [ SYSNAME
                                              , CHECKDEADLOCK
                                              , FAULTFAIRDISABLE
                                              , MODULEWFAIRDISABLE ], \
                      keyword("ENDOPTIONS")
                      
def SYSNAME():              return [("SYSNAME", re.compile(r"[\w\.\d\_]*"))]
def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]
def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]
def MODULEWFAIRDISABLE():   return [re.compile(r"INST_WEAK_FAIR_DISABLE")]


# DEFINES ---------------------------------------------------------------------
def DEFINE():       return keyword("DEFINE"), NAME, ":=", EXPRESION



# PROCTYPES ###################################################################

def PROCTYPE():     return keyword("PROCTYPE"), NAME, "(", CTXVARS, \
                           SYNCACTS, ")", PROCTYPEBODY, \
                           keyword("ENDPROCTYPE")

#..............................................................................
def CTXVARS():      return 0, (NAME, -1, (",", NAME))

#..............................................................................
def SYNCACTS():     return 0, (";", 0, ( NAME, -1, (",", NAME)))

#..............................................................................
#TODO quizas seria mejor no dar un orden para las secciones:
def PROCTYPEBODY(): return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS

#..............................................................................
def VAR():          return keyword("VAR"), -1, VARDECL
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:

#..............................................................................
def VARDECL():      return NAME, r":", [ BOOLEANT, ENUMT, RANGET, ARRAYT], r";"

#..............................................................................
def BOOLEANT():     return [keyword("boolean")]

#..............................................................................
def ENUMT():        return re.compile(r"\{"), 0, ([NAME, INT]\
                           , -1, (re.compile(r"\,") \
                           , [NAME, INT])), re.compile(r"\}")

#..............................................................................
def ARRAYT():       return re.compile(r"array"), INT, re.compile(r"\.\."), INT \
                           , re.compile(r"of\b"), [RANGET, BOOLEANT, ENUMT]
#TODO RANGET es lo mismo que range, pero tiene otro sentido:

#..............................................................................
def RANGET():        return INT, re.compile(r"\.\."), INT

#..............................................................................
def FAULT():        return keyword("FAULT"), -1, FAULTDECL
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:

#..............................................................................
def FAULTDECL():    return NAME, ":", 0, (0, EXPRESION, "=>", 0, NEXTLIST) \
                           , keyword("is"), [BYZ, STOP, TRANSIENT], r";"

#..............................................................................
def BYZ():          return keyword("BYZ"), "(", NAME, -1, (",", NAME), ")"

#..............................................................................
def TRANSIENT():    return [keyword("TRANSIENT")]

#..............................................................................
def STOP():         return [(keyword("STOP"), "(", NAME, -1 \
                           , (",", NAME), ")"), keyword("STOP")]

#..............................................................................
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:
def INIT():         return keyword("INIT"), 0, EXPRESION, r";"

#..............................................................................
def TRANS():        return keyword("TRANS"), -1, TRANSDECL
#TODO el ; aca si es necesario para no confundir los corchetes del nombre
# de transicion con los de subscription:

#..............................................................................
def TRANSDECL():    return r"[", 0, NAME, r"]", r":" \
                            , 0, EXPRESION, 0, (r"=>", NEXTLIST), r";"


# INSTANCES -------------------------------------------------------------------

def INSTANCE():     return keyword("INSTANCE"), NAME, "=", NAME \
                           , "(", PARAMLIST, ")"
def PARAMLIST():    return 0, ( EXPRESION, -1, ( ",", EXPRESION))




# PROPERTIES DECLARATION ######################################################


def EXPLAIN():
    """ Human readible name or description of the properties for better 
        understanding.
    """
    return [("#", re.compile(r"[\w\s]*"))]


def PROPERTY():       return [([ LTLSPEC
                               , CTLSPEC
                               , NORMALBEHAIVIOUR
                               , FINMANYFAULTS
                               , FINMANYFAULT]
                              , 0, EXPLAIN, r";")]


# CTL
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


# LTL
ltlbinops = re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
ltluops = re.compile(r"\!|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")

#TODO dar nombre a las props: (keyword("LTLSPECNAME"), IDENT, ":=", LTLEXP)]:
def LTLSPEC():      return [(keyword("LTLSPEC"), LTLEXP)] 
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , ltlbinops, LTLEXP
def LTLUOP():       return -1 , ltluops, LTLVAL
def LTLVAL():       return [ EXPRESION 
                           , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) 
                           ]



# common properties ###########################################################

# TODO check for the correct time expresion in this cases, for example only 
# LTLEXP can be used for FINMANYFAULTS.
def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "->",\
                               [LTLEXP, CTLEXP]
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "->",\
                               [LTLEXP, CTLEXP]
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT") \
                               , "(", IDENT, -1, (",", IDENT), ")", "->"\
                               , [LTLEXP, CTLEXP]




# CONTRAINTS ##################################################################
def CONSTRAINT():   return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(keyword("FAIRNESS"), EXPRESION)]
def COMPASSION():   return keyword("COMPASSION") \
                           , "(", EXPRESION, ",", EXPRESION, ")"






# -----------------------------------------------------------------------------
# TESTS .......................................................................
# -----------------------------------------------------------------------------

if __name__ == "__main__":

    def TEST(): return [ SYSTEM ]

    _file = fileinput.input()

    print "Parsing ...."

    _ast = parse(TEST, _file, True, COMMENT, packrat = True)

    print "Parsed:\n\n",_ast , "\n"

    debugGREEN(_ast)

    debugLBLUE(_str(_ast))

    if len(_ast) and _ast[0].__name__ == EXPRESION:
        debugRED(putBrackets(_ast[0]))

