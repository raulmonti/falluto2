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
import pyPEG
import re, fileinput
from DebugRepair import *
import UtilsRepair
from Utils import _cl, _str, putBrackets
#
#===============================================================================


# TODO Notar que no estoy verificando solo sintaxis aca --->> eso esta muy mal
# Asegurarse de que solo se revise la estructura sintáctica, y no la
# semantica ni nada por el estilo.

# TODO Everything should be in english (or everyone will hate me). I'm proud
# of my beautiful language though.

# SOME DEFINITIONS #############################################################

cp = re.compile


################################################################################

def GRAMMAR():
    """ This is the grammar rule to parse for Falluto2.0. """
    return [MODEL] # Brackets so we don't ommit the big Symbol

#..............................................................................
def COMMENT():
    """ Comments syntax for Falluto2.0., just as in C :D. """
    return [ re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]

#..............................................................................
def BL():
    """ Consume blanks (\n \t\r...)"""
    return re.compile('[\s]+')

B  = -1, [BL, COMMENT] # Definition to ovoid obligation of blanks and COMMENTS

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
def SUBSCRIPT():
    """ List subscripts, to access its elements. Subscripts opening bracket
        should be just after the list name, no white spaces would be tolerated
        beteween the list name and the opening bracket.
    """
    return pyPEG._not(re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?\s+")),\
           IDENT, re.compile(r"\["), B, [IDENT, INT], B, re.compile(r"\]")

#..............................................................................
def NEXTREF():
    """ A reference to the value of a variable in the next state.
    """
    return [([SUBSCRIPT,IDENT], "'")]

#..............................................................................
def SET(): return re.compile(r"\{"), B, 0, ([SUBSCRIPT, IDENT, INT, BOOL]\
               , -1, (B, re.compile(r"\,"), B\
               , [SUBSCRIPT, IDENT, INT, BOOL])), B, re.compile(r"\}")

#..............................................................................
def RANGE(): return INT, re.compile(r"\.\."), INT

#..............................................................................
def INCLUSION(): return [SUBSCRIPT,IDENT], B, re.compile(r"\bin\b"), B\
                        , [SET,RANGE]

# EXPRESION ###################################################################

def EXPRESION(): return [PROP]

#..............................................................................
def VALUE():    return [ (re.compile(r"\("), B, PROP, B, re.compile(r"\)"))
                       , INCLUSION
                       , NEXTREF
                       , SUBSCRIPT
                       , IDENT
                       , INT
                       , BOOL
                       , EVENT
                       , (re.compile(r"\!"), B, VALUE)
                       , (re.compile(r"\-"), B, VALUE)
                       ]

#..............................................................................
def PROD():     return [ ( VALUE, 0, ( B, re.compile(r"\*|\/|\%"), B, PROD)) ]

#..............................................................................
def SUM():      return [ ( PROD, 0, ( B, re.compile(r"\+|\-"), B, SUM)) ]

#..............................................................................
def COMP():     return [ ( SUM, 0, 
                           ( B, re.compile(r"(?!\=\>)\=|\!\=|\>\=|\<\=|\<|\>")
                           , B, COMP 
                           )
                         ) 
                       ]

#..............................................................................
def LOGIC():    return [ ( COMP, 0, ( B, re.compile(r"\||\&"), B, LOGIC)) ]

#..............................................................................
def PROP():     return [ ( LOGIC, 0, ( B, re.compile(r"\-\>|\<\-\>"), B
                                        , PROP
                                        )
                         )
                       ]

#..............................................................................
def NEXTLIST():     return NEXTASSIGN, -1, ( B, ",", B, NEXTASSIGN)

#..............................................................................
def NEXTASSIGN():   return NEXTREF, B,\
                            [ (re.compile(r"\="), B, EXPRESION)
                            , (re.compile(r"in"), B, [ SET, RANGE])
                            ]


# MODEL SINTAX ################################################################
def MODEL(): return B, 0, OPTIONS , -1, ( B, [ DEFINE
                                             , PROCTYPE
                                             , INSTANCE
                                             , PROPERTY
                                             , CONSTRAINT ]) , B

# OPTIONS ---------------------------------------------------------------------
def OPTIONS(): return keyword("OPTIONS"), -1, ( B, [ MODNAME
                                                   , CHECKDEADLOCK
                                                   , FAULTFAIRDISABLE
                                                   , MODULEWFAIRDISABLE 
                                                   ]
                                              ), B, keyword("ENDOPTIONS")
                      
def MODNAME():              return [("MODELNAME", B
                                    , re.compile(r"[\w\.\d\_]*"))]
def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]
def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]
def MODULEWFAIRDISABLE():   return [re.compile(r"INST_WEAK_FAIR_DISABLE")]


# DEFINES ---------------------------------------------------------------------
def DEFINE():       return keyword("DEFINE"), B, NAME, B, EXPRESION

# PROCTYPES ###################################################################

def PROCTYPE():     return keyword("PROCTYPE"), B, NAME, B, "(", B, CTXVARS, \
                           B, SYNCACTS, B, ")", B, PROCTYPEBODY, B, \
                           keyword("ENDPROCTYPE")

#..............................................................................
def CTXVARS():      return 0, (NAME, -1, ( B, ",", B, NAME))

#..............................................................................
def SYNCACTS():     return 0, (";", 0, ( B, NAME, -1, ( B, ",", B, NAME)))

#..............................................................................
#TODO quizas seria mejor no dar un orden para las secciones:
def PROCTYPEBODY(): return 0, VAR, 0, (B, FAULT), 0, ( B, INIT), 0, ( B, TRANS)

#..............................................................................
def VAR():          return keyword("VAR"), -1, ( B, VARDECL)

#..............................................................................
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:
def VARDECL():      return NAME, B, r":", B, [ BOOLEANT, ENUMT, RANGET, ARRAYT]\
                           , B, r";"

#..............................................................................
def BOOLEANT():     return [keyword("boolean")]

#..............................................................................
def ENUMT():        return re.compile(r"\{"), 0, ( B, [NAME, INT]\
                           , -1, ( B, re.compile(r"\,") \
                           , B, [NAME, INT])), B, re.compile(r"\}")

#..............................................................................
def ARRAYT():       return re.compile(r"array"), B, INT, re.compile(r"\.\.")\
                           , INT, B\
                           , re.compile(r"of\b"), B, [RANGET, BOOLEANT, ENUMT]
#TODO RANGET es lo mismo que range, pero tiene otro sentido:

#..............................................................................
def RANGET():        return INT, re.compile(r"\.\."), INT

#..............................................................................
def FAULT():        return keyword("FAULT"), -1, ( B, FAULTDECL)
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:

#..............................................................................
def FAULTDECL():    return NAME, B, ":", 0, ( B, 0, EXPRESION, B, "=>"\
                           , 0, ( B, NEXTLIST)), B\
                           , keyword("is"), B, [BYZ, STOP, TRANSIENT], B, r";"

#..............................................................................
def BYZ():          return keyword("BYZ"), B, "(", B, NAME\
                           , -1, ( B, ",", B, NAME), B, ")"

#..............................................................................
def TRANSIENT():    return [keyword("TRANSIENT")]

#..............................................................................
def STOP():         return [(keyword("STOP"), B, "(", B, NAME, -1 \
                           , ( B, ",", B, NAME), B, ")"), keyword("STOP")]

#..............................................................................
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:
def INIT():         return keyword("INIT"), 0, ( B, EXPRESION), B, r";"

#..............................................................................
def TRANS():        return keyword("TRANS"), -1, ( B, TRANSITION)
#TODO el ; aca si es necesario para no confundir los corchetes del nombre
# de transicion con los de subscription:

#..............................................................................
def TRANSITION():    return cp(r"\["), 0,( B, NAME), B, cp(r"\]"), B, cp(r"\:")\
                            , ( B, 0, EXPRESION), 0, ( B, cp(r"\=\>"), B\
                            , NEXTLIST), B, cp(r"\;")


# INSTANCES -------------------------------------------------------------------

def INSTANCE():     return keyword("INSTANCE"), B, NAME, B, "=", B, NAME \
                           , B, cp(r"\("), B, PARAMLIST, B, cp(r"\)")
def PARAMLIST():    return 0, ( EXPRESION, -1, ( B, cp(r"\,"), B, EXPRESION))




# PROPERTIES DECLARATION ######################################################


def EXPLAIN():
    """ Human readible name or description of the properties for better 
        understanding.
    """
    return [(cp(r'\"'), re.compile(r"[\w\s]*"), cp(r'\"'))]


def PROPERTY():       return [([ LTLSPEC
                               , CTLSPEC
                               , NORMALBEHAIVIOUR
                               , FINMANYFAULTS
                               , FINMANYFAULT]
                              , 0, ( B, EXPLAIN), B, r";")]


# CTL
CTLUNOP = r"""
                \! | \bEG\b | \bEX\b | \bEF\b | \bAG\b | \bAX\b | \bAF\b
           """

CTLBINOP = r"""
                \& | \| | \bxor\b | \bxnor\b | \-\> | \<\-\>
           """


def CTLSPEC():          return [(keyword("CTLSPEC"), B, CTLEXP)]
def CTLEXP():           return [ ( CTLVALUE, B, re.compile(CTLBINOP,re.X)
                                 , B, CTLEXP
                                 )
                               , ( re.compile(r"\bE\b|\bA\b"), B \
                                 , re.compile(r"\["), B \
                                 , CTLEXP, B, re.compile(r"\bU\b"), B, CTLEXP\
                                 , B, re.compile(r"\]")
                                 )
                               , CTLVALUE
                               ]
def CTLVALUE():         return [ (re.compile(CTLUNOP,re.X), B, CTLEXP)
                               , (re.compile(r"\("), B, CTLEXP, B
                                 , re.compile(r"\)"))
                               , EXPRESION
                               ]


# LTL
ltlbinops = re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
ltluops = re.compile(r"\!|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")

def LTLSPEC():      return [(keyword("LTLSPEC"), B, LTLEXP)] 
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , B, ltlbinops, B, LTLEXP
 # TODO may need to force space between unary operators in LTLUOP
def LTLUOP():       return -1 ,(B, ltluops), B, LTLVAL
def LTLVAL():       return [ EXPRESION, (re.compile(r"\("), B
                           , LTLEXP, B, re.compile(r"\)")) 
                           ]



# common properties ###########################################################

# TODO check for the correct time expresion in this cases, for example only 
# LTLEXP can be used for FINMANYFAULTS.
def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), B, "->", B,\
                               [LTLEXP, CTLEXP]
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), B, "->", B,\
                               [LTLEXP, CTLEXP]
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT"), B \
                               , "(", B, IDENT, -1, ( B, ",", B, IDENT)\
                               , B, ")", B, "->", B, [LTLEXP, CTLEXP]




# CONTRAINTS ##################################################################
def CONSTRAINT():   return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(keyword("FAIRNESS"), B, EXPRESION)]
def COMPASSION():   return keyword("COMPASSION"), B, "(", B, EXPRESION,\
                           B, ",", B, EXPRESION, B, ")"






# -----------------------------------------------------------------------------
# TESTS .......................................................................
# -----------------------------------------------------------------------------

if __name__ == "__main__":

    def TEST():
        """ Test the full GRAMMAR """
        return [GRAMMAR]

    def TEST1():
        """ Test a SUBSCRIPT followed by an INCLUSION """
        return [(B, SUBSCRIPT, B, INCLUSION, B)]

    def TEST2():
        """ Test sets one after the other """
        return [(-1,(B, SET, B))]

    def TEST3():
        """ Test an expresion """
        return [(B, EXPRESION, B)]

    def TEST4():
        """ Test a definition """
        return [(B,DEFINE,B)]

    def TEST5():
        """ Test comments """
        return [( B, COMMENT ,B,re.compile("ALGO"), B)]

    _file = fileinput.input()

    print "Parsing ...."

    _ast = parse(TEST, _file, False, packrat = False)

    print _ast#, "pyAST len = {0}, Set len {1}".format(len(_ast), len(_ast[1].what))

    debugCURRENT(UtilsRepair.ss(_ast))
#    print "Parsed:\n\n",_ast , "\n"

#    debugGREEN(_ast)

#    debugLBLUE(_str(_ast))

#    if len(_ast) and _ast[0].__name__ == EXPRESION:
#        debugRED(putBrackets(_ast[0]))

"""°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°"""
# FIXME skipcomments from pyPEG has some problems with white spaces consuming,
#       i.e. the grammar breaks down when using 'B' in it and parsing with
#       skipcomments option.

