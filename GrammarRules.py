# -*- coding: utf-8 -*-

# Modulo GrammarRules.py
# 24 de Octubre del 2013
# Autor: Raul Monti
# F A L L U T O    2 . 0
#
# En este modulo se determinan las reglas sintacticas del lenguaje de 
# falluto2.0, las cuales seran interpretadas por la libreria PyPEG.
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
                        \bin\b|\bjust\b|\bis\b|\barray\b|\bof\b|\bPROPERTIE\b

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
           SUBSCRIPTED, -2,\
           (re.compile(r"\["), B, SUBSCRIPTOR, B, re.compile(r"\]"))

def SUBSCRIPTED():
    return IDENT

def SUBSCRIPTOR():
    return [IDENT, INT]

#..............................................................................
def NEXTREF():
    """ A reference to the value of a
        variable in the next state.
    """
    return [(REFERENCE, cp(r"\'"))]

def REFERENCE():
    return [SUBSCRIPT,IDENT]

#..............................................................................
def SET():
    """ Sets of symbols, integers and booleans """
    return re.compile(r"\{"), B, 0\
           , ( SETMEMBER, -1, (B, re.compile(r"\,"), B, SETMEMBER))\
           , B, re.compile(r"\}")

def SETMEMBER():
    return [SUBSCRIPT, IDENT, INT, BOOL]

#..............................................................................
def RANGE(): return START, re.compile(r"\.\."), END

def START(): return INT

def END(): return INT

#..............................................................................
def INCLUSION(): return INCLUDED, B, re.compile(r"\bin\b"), B, INCLUDING

def INCLUDED(): return [SUBSCRIPT,IDENT]

def INCLUDING(): return [SET,RANGE]

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
def OPTIONS():  return cp("OPTIONS"), -1, ( B, OPT
                                         ), B, cp("ENDOPTIONS")

def OPT():      return [ MODNAME
                       , CHECKDEADLOCK
                       , FAULTFAIRDISABLE
                       , MODULEWFAIRDISABLE 
                       ]

def MODNAME():              return [(cp(r"MODELNAME"), B, MNAME)]

def MNAME():                return re.compile(r"[\w\.\d\_]*")

def CHECKDEADLOCK():        return [re.compile(r"CHECK_DEADLOCK")]

def FAULTFAIRDISABLE():     return [re.compile(r"FAULT_FAIR_DISABLE")]

def MODULEWFAIRDISABLE():   return [re.compile(r"INST_WEAK_FAIR_DISABLE")]

# DEFINES =====================================================================#

def DEFINE():       return cp("DEFINE"), B, NAME, B, DEF

def DEF():          return [ EXPRESION, SET, RANGE]

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
def VARDECL():      return NAME, B, cp(r"\:"),\
                           B, VTYPE

def VTYPE():        return [ BOOLEANT, ENUMT, RANGET, ARRAYT]

#..............................................................................
def BOOLEANT():     return [cp("boolean")]

#..............................................................................
def ENUMT():        return re.compile(r"\{"), 0, ( B, [NAME, INT]\
                           , -1, ( B, re.compile(r"\,") \
                           , B, [NAME, INT])), B, re.compile(r"\}")

#..............................................................................
def ARRAYT():       return re.compile(r"array"), B, START, re.compile(r"\.\.")\
                           , END, B\
                           , re.compile(r"of\b"), B, VTYPE
#TODO RANGET es lo mismo que range, pero tiene otro sentido:

#..............................................................................
def RANGET():        return START, re.compile(r"\.\."), END

#..............................................................................
def FAULT():        return cp("FAULT"), -1, ( B, FAULTDECL)

#..............................................................................
def FAULTDECL():    return NAME, B, cp(r"\:"), 0, ( B, 0, PRE, B\
                           , cp(r"\=\>"), 0, ( B, POS)), B\
                           , cp("is"), B, FTYPE

def PRE():          return EXPRESION

def POS():          return NEXTLIST

def FTYPE():        return [BYZ, STOP, TRANSIENT]

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
def INIT():         return cp("INIT"), 0, ( B, EXPRESION)

#..............................................................................
def TRANS():        return cp("TRANS"), -1, ( B, TRANSITION)

#..............................................................................
def TRANSITION():    return cp(r"\["), 0,( B, NAME), B, cp(r"\]"), B, cp(r"\:")\
                            , ( B, 0, PRE), 0, ( B, cp(r"\=\>"), B\
                            , POS)


# INSTANCES -------------------------------------------------------------------
def INSTANCE():     return cp("INSTANCE"), B, NAME, B, cp(r"\="), B, PROCNAME\
                           , B, cp(r"\("), B, PARAMLIST, B, cp(r"\)")

def PROCNAME():     return NAME

def PARAMLIST():    return 0, ( EXPRESION, -1, ( B, cp(r"\,"), B, EXPRESION))

# PROPERTIES DECLARATION ======================================================#


def EXPLAIN():
    """ Human readible name or description of the properties for better 
        understanding.
    """
    return [(cp(r'\"'), re.compile(r"[\w\s\-\_]*"), cp(r'\"'))]


def PROPERTY():     return [(cp("PROPERTY"), B, 0, PROPNAME, B, cp(r"="), B,
                             [ LTLSPEC
                             , CTLSPEC
                             , NORMALBEHAIVIOUR
                             , FINMANYFAULTS
                             , FINMANYFAULT
                             , ENSURE
                             , ATMOST ]
                            , 0, ( B, EXPLAIN))]

def PROPNAME():     return [NAME]

# CTL
CTLUNOP = r""" \! | \bEG\b | \bEX\b | \bEF\b | \bAG\b | \bAX\b | \bAF\b """

CTLBINOP = r""" \& | \| | \bxor\b | \bxnor\b | \-\> | \<\-\> """

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

# META PROPERTIES =============================================================#

# TODO check for the correct time expresion in this cases, for example only 
# LTLEXP can be used for FINMANYFAULTS.
def NORMALBEHAIVIOUR(): return cp("NORMAL_BEHAIVIOUR"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]

def FINMANYFAULTS():    return cp("FINITELY_MANY_FAULTS"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]

def FINMANYFAULT():     return cp("FINITELY_MANY_FAULT"), B \
                               , cp(r"\("), B, FNAME, -1, ( B, cp(r"\,"), B\
                               , FNAME), B, cp(r"\)"), B, cp(r"\-\>")\
                               , B, [LTLEXP, CTLEXP]

def FNAME():            return IDENT

def ATMOST():           return cp(r'ATMOST'), B, cp(r'\('), B, LIMIT, B,\
                               -1, (B, cp(r'\,'), B, FNAME), B,\
                               cp(r'\)'), B, cp(r'\-\>'), B, [LTLEXP, CTLEXP]

def ENSURE():           return cp(r'ENSURE'), B, cp(r'\('), B, LIMIT,\
                               -1, (B, cp(r'\,'), B, ANAME), B,\
                               cp(r'\)'), B, cp(r'WITHOUT'), B, cp(r'\('),\
                               0, (B, FNAME, -1, (B, cp(r'\,'), B, FNAME)),\
                               B, cp(r'\)'), B, cp(r'\-\>'), B, [LTLEXP, CTLEXP]

def LIMIT():            return INT

def ANAME():            return IDENT

# CONTRAINTS ==================================================================#
def CONSTRAINT():   return [FAIRNESS, COMPASSION]

def FAIRNESS():     return [(cp("FAIRNESS"), B, EXPRESION)]

def COMPASSION():   return cp("COMPASSION"), B, cp(r"\("), B, IMPLYING,\
                           B, cp(r"\,"), B, IMPLIED, B, cp(r"\)")

def IMPLYING():     return EXPRESION

def IMPLIED():      return EXPRESION


# UTILS ========================================================================
def compiles( string="", rule=None):
    """ Returns True if string compiles under rule, False otherwise. """
    _ast = None
    try:
        _ast = pyPEG.parseLine(string, rule, [], False, COMMENT, False)
    except:
        return False

    return True

#===============================================================================
# TESTS ========================================================================
#===============================================================================

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


"""°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°°"""
# FIXME skipcomments from pyPEG has some problems with white spaces consuming,
#       i.e. the grammar breaks down when using 'B' in it and parsing with
#       skipcomments option.

# FIXME comments and blanks can't be treated the same as they are being treated
#       at 'B'
