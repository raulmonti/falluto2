# -*- coding: utf-8 -*-

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


from pyPEG import *
import pyPEG
import re, fileinput
from Debug import *
import Utils


#===============================================================================


# TODO Notar que no estoy verificando solo sintaxis aca --->> eso esta muy mal
# Asegurarse de que solo se revise la estructura sintáctica, y no la
# semantica ni nada por el estilo.

# TODO Everything should be in english (or everyone will hate me). I'm proud
# of my beautiful language though.


# SOME DEFINITIONS ============================================================#

cp = re.compile


#==============================================================================#

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

# IDENTIFIERS =================================================================#
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
           IDENT, -1, (re.compile(r"\["), B, [IDENT, INT], B, re.compile(r"\]"))


#..............................................................................
def NEXTREF():
    """ A reference to the value of a variable in the next state.
    """
    return [([SUBSCRIPT,IDENT], cp(r"\'"))]

#..............................................................................
def SET(): return re.compile(r"\{"), B, 0, ([SUBSCRIPT, IDENT, INT, BOOL]\
               , -1, (B, re.compile(r"\,"), B\
               , [SUBSCRIPT, IDENT, INT, BOOL])), B, re.compile(r"\}")

#..............................................................................
def RANGE(): return INT, re.compile(r"\.\."), INT

#..............................................................................
def INCLUSION(): return [SUBSCRIPT,IDENT], B, re.compile(r"\bin\b"), B\
                        , [SET,RANGE]

# EXPRESION ===================================================================#

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
def NEXTLIST():     return NEXTASSIGN, -1, ( B, cp(r"\,"), B, NEXTASSIGN)

#..............................................................................
def NEXTASSIGN():   return NEXTREF, B,\
                            [ (re.compile(r"\="), B, EXPRESION)
                            , (re.compile(r"in"), B, [ SET, RANGE])
                            ]


# MODEL SINTAX ================================================================#
def MODEL(): return B, 0, OPTIONS , -1, ( B, [ DEFINE
                                             , PROCTYPE
                                             , INSTANCE
                                             , PROPERTY
                                             , CONSTRAINT ]) , B

# OPTIONS =====================================================================#
def OPTIONS(): return cp("OPTIONS"), -1, ( B, [ MODNAME
                                                   , CHECKDEADLOCK
                                                   , FAULTFAIRDISABLE
                                                   , MODULEWFAIRDISABLE 
                                                   ]
                                              ), B, cp("ENDOPTIONS")
                      
def MODNAME():              return [(cp(r"MODELNAME"), B
                                    , re.compile(r"[\w\.\d\_]*"))]
def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]
def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]
def MODULEWFAIRDISABLE():   return [re.compile(r"INST_WEAK_FAIR_DISABLE")]


# DEFINES =====================================================================#
def LINE():         return cp(r"[^\r\n]*")
# FIXME watch out!! LINE will get all the spaces at the end of the line as part
# of the definition.

def DEFINE():       return cp("DEFINE"), B, NAME, B, [ EXPRESION
                                                     , SET
                                                     , RANGE
                                                     ]

# PROCTYPES ===================================================================#

def PROCTYPE():     return cp("PROCTYPE"), B, NAME, B, cp(r"\("), B\
                           , CTXVARS, B, SYNCACTS, B, cp(r"\)"), B\
                           , PROCTYPEBODY, B, cp("ENDPROCTYPE")

#..............................................................................
def CTXVARS():      return 0, (NAME, -1, ( B, cp(r"\,"), B, NAME))

#..............................................................................
def SYNCACTS():     return 0, (cp(r"\;"), 0\
                           , ( B, NAME, -1, ( B, cp(r"\,"), B, NAME)))

#..............................................................................
#TODO It may be better not to give an order to the sections.
def PROCTYPEBODY(): return 0, VAR, 0, (B, FAULT), 0, ( B, INIT), 0, ( B, TRANS)

#..............................................................................
def VAR():          return cp("VAR"), -1, ( B, VARDECL)

#..............................................................................
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:
def VARDECL():      return NAME, B, cp(r"\:"),\
                           B, [ BOOLEANT, ENUMT, RANGET, ARRAYT], B, cp(r"\;")

#..............................................................................
def BOOLEANT():     return [cp("boolean")]

#..............................................................................
def ENUMT():        return re.compile(r"\{"), 0, ( B, [NAME, INT]\
                           , -1, ( B, re.compile(r"\,") \
                           , B, [NAME, INT])), B, re.compile(r"\}")

#..............................................................................
def ARRAYT():       return re.compile(r"array"), B, INT, re.compile(r"\.\.")\
                           , INT, B\
                           , re.compile(r"of\b"), B, [ ARRAYT
                                                     , RANGET
                                                     , BOOLEANT
                                                     , ENUMT]
#TODO RANGET es lo mismo que range, pero tiene otro sentido:

#..............................................................................
def RANGET():        return INT, re.compile(r"\.\."), INT

#..............................................................................
def FAULT():        return cp("FAULT"), -1, ( B, FAULTDECL)
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:

#..............................................................................
def FAULTDECL():    return NAME, B, cp(r"\:"), 0, ( B, 0, EXPRESION, B\
                           , cp(r"\=\>"), 0, ( B, NEXTLIST)), B\
                           , cp("is"), B, [BYZ, STOP, TRANSIENT]\
                           , B, cp(r"\;")

#..............................................................................
def BYZ():          return cp("BYZ"), B, cp(r"\("), B, NAME\
                           , -1, ( B, cp(r"\,"), B, NAME), B, cp(r"\)")

#..............................................................................
def TRANSIENT():    return [cp("TRANSIENT")]

#..............................................................................
def STOP():         return [(cp("STOP"), B, cp(r"\("), B, NAME, -1 \
                           , ( B, cp(r"\,"), B, NAME), B, cp(r"\)"))\
                           , cp("STOP")]

#..............................................................................
#TODO el ; al final quizas no sea necesario, pero me parece que queda
# de alguna manera mas consistente si todas las declaraciones terminan en ;
# y no solo las transiciones:
def INIT():         return cp("INIT"), 0, ( B, EXPRESION), B, cp(r"\;")

#..............................................................................
def TRANS():        return cp("TRANS"), -1, ( B, TRANSITION)
#TODO el ; aca si es necesario para no confundir los corchetes del nombre
# de transicion con los de subscription:

#..............................................................................
def TRANSITION():    return cp(r"\["), 0,( B, NAME), B, cp(r"\]"), B, cp(r"\:")\
                            , ( B, 0, EXPRESION), 0, ( B, cp(r"\=\>"), B\
                            , NEXTLIST), B, cp(r"\;")


# INSTANCES -------------------------------------------------------------------
def INSTANCE():     return cp("INSTANCE"), B, NAME, B, cp(r"\="), B, NAME\
                           , B, cp(r"\("), B, PARAMLIST, B, cp(r"\)")
def PARAMLIST():    return 0, ( EXPRESION, -1, ( B, cp(r"\,"), B, EXPRESION))

# PROPERTIES DECLARATION ======================================================#


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
                              , 0, ( B, EXPLAIN), B, cp(r"\;"))]

# CTL
CTLUNOP = r"""
                \! | \bEG\b | \bEX\b | \bEF\b | \bAG\b | \bAX\b | \bAF\b
           """

CTLBINOP = r"""
                \& | \| | \bxor\b | \bxnor\b | \-\> | \<\-\>
           """

def CTLSPEC():          return [(cp("CTLSPEC"), B, CTLEXP)]
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

def LTLSPEC():      return [(cp("LTLSPEC"), B, LTLEXP)] 
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , B, ltlbinops, B, LTLEXP
 # TODO may need to force space between unary operators in LTLUOP
def LTLUOP():       return -1 ,(B, ltluops), B, LTLVAL
def LTLVAL():       return [ EXPRESION, (re.compile(r"\("), B
                           , LTLEXP, B, re.compile(r"\)")) 
                           ]



# COMMON PROPERTIES ===========================================================#

# TODO check for the correct time expresion in this cases, for example only 
# LTLEXP can be used for FINMANYFAULTS.
def NORMALBEHAIVIOUR(): return cp("NORMAL_BEHAIVIOUR"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]
def FINMANYFAULTS():    return cp("FINITELY_MANY_FAULTS"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]
def FINMANYFAULT():     return cp("FINITELY_MANY_FAULT"), B \
                               , cp(r"\("), B, IDENT, -1, ( B, cp(r"\,"), B\
                               , IDENT), B, cp(r"\)"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]

# CONTRAINTS ##################################################################
def CONSTRAINT():   return [FAIRNESS, COMPASSION]
def FAIRNESS():     return [(cp("FAIRNESS"), B, EXPRESION)]
def COMPASSION():   return cp("COMPASSION"), B, cp(r"\("), B, EXPRESION,\
                           B, cp(r"\,"), B, EXPRESION, B, cp(r"\)")

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


    def TEST6():
        """ Test PROPERTY """
        return [( B, PROPERTY, B)]


    _file = fileinput.input()

    print "Parsing ...."

    _ast = parse(TEST6, _file, False, packrat = False)

    print _ast
#    for x in Utils.getAst(_ast,[u'DEFINE']):
#        debug("debugRED", x)
#        print ""

#    debug("debugGREEN",\
#         Utils.ast2str(Utils.getAst(_ast,[u'COMMENT'])))



"""°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°"""
# FIXME skipcomments from pyPEG has some problems with white spaces consuming,
#       i.e. the grammar breaks down when using 'B' in it and parsing with
#       skipcomments option.


# FIXME comments and blanks can't be treated the same as they are being treated
#       at 'B'
