#===============================================================================
# Modulo GrammarRules.py
# 7 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

"""
    En este modulo se determinan las reglas gramaticales que definen la 
    gramatica de entrada para falluto. Las reglas seran interpretadas por
    la libreria PyPEG.
"""

import InputManager.pyPEG
from InputManager.pyPEG.pyPEG import keyword, _and, _not
import re
from Debug import *
from Config import *

if DEBUGTODO__:
    DebugTODO("Dar la opcion de dar nombre al systema.fll dentro del" +\
              "systema, por ejemplo usando la etiqueta fllname seguida" +\
              " del nombre.\n")
    DebugTODO("Aceptar numeros como parametros en las instancias si es que" +\
              " se debe\n")
    DebugTODO("Esta falla se rompe y esta bien escrita: " +\
              " f_1 : TRUE : next(localv1) = (TRUE | FALSE = 1>2)\n")


#///////////////////////////////////////////////////////////////////////////////
#   LENGUAGE (EN PEG)
#


#IDENTIFIERS
identifiers = r"(?!\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bnext\b|\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"
def IDENT():        return re.compile(identifiers)
def INT():          return re.compile(r"\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")


#MATH FORMULA
# Los operadores anidan a derecha, no doy prioridades ya que no vienen el caso
# despues que se las arregle NuSMV o que quien sea. 
mathbinop = r"\+|\-|\*|\/|\%"
def MATH():         return [MATHBINOP, MATHVAL]
def MATHBINOP():    return MATHVAL , re.compile(mathbinop), MATH
def MATHVAL():      return [ INT, IDENT, (re.compile(r"\("), MATH, re.compile(r"\)")), (re.compile(r"\-"), MATH)]


#BOOLEAN FORMULA
booleanop = r"\<\=|\>\=|\<(?!->)|\>|\=|\!\="
def BOOLEXP():      return [BOOLBINOP, BOOLVAL]
def BOOLBINOP():    return BOOLVAL, re.compile(booleanop), BOOLEXP
def BOOLVAL():      return [ BOOL, IDENT, MATH, (re.compile(r"\("), BOOLEXP, re.compile(r"\)")), (re.compile(r"\!"), BOOLEXP), (MATH , re.compile(booleanop), MATH) ]


#PROPOSITIONAL FORMULA
propbinop = r"\-\>|\&|\||\<\-\>"
def PROPFORM():     return [PROPBINOP, PROPVAL]
def PROPBINOP():    return PROPVAL, re.compile(propbinop), PROPFORM
def PROPVAL():      return [BOOLEXP, (re.compile(r"\("), PROPFORM, re.compile(r"\)")), (re.compile(r"\!"), PROPFORM)]


#NEXT PROPOSITIONAL FORMULA
def NEXTPROPFORM(): return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return keyword("next"), "(", IDENT, ")", "=", \
                           [ IDENT, SET, NEXTREF, MATH, PROPFORM]
def NEXTREF():      return keyword("next"), "(", IDENT, ")"
if DEBUGTODO__:
    DebugTODO("Revisar si se le puede asignar un RANGE a un NEXTVAL en NuSMV "+\
              "y si es asi agregarlo en la regla gramatical correspondiente.")

#VAR TYPES
def SET():          return "{", [IDENT, INT], -1, (",", [IDENT, INT]), "}"      #En NuSMV enumeration types no se pueden usar las palabras reservadas
def RANGE():        return INT, "..", INT
def BOOLEAN():      return "bool"


#SYSTEM
def SYSTEM():       return -1, [MODULE, INSTANCE, LTLSPEC, FAIRNESS, COMPASSION]


#MODULE
def MODULE():       return keyword("MODULE"), IDENT, "(", CONTEXTVARS, CONTEXTACTS, ")", MODULEBODY
def CONTEXTVARS():  return 0, (IDENT, -1, (",", IDENT))
def CONTEXTACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS

def VAR():          return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, ":", [ BOOLEAN, SET, RANGE]

def FAULT():        return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return IDENT, ":", 0, PROPFORM, ":", 0, NEXTPROPFORM

def INIT():         return keyword("INIT"), 0, PROPFORM

def TRANS():        return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":", 0, PROPFORM, ":", 0, NEXTPROPFORM, -1, PFAULTDECL
def PFAULTDECL():   return "..", [BIZ, STOP], ".."
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def STOP():         return "STOP", "(", IDENT, ")"


#INSTANCE
def INSTANCE():     return keyword("INSTANCE"), IDENT, "=", IDENT, "(", PARAMLIST, ")"
instparams = [re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"), re.compile(r"\d+")]
def PARAMLIST():    return 0, ( instparams, -1, ( ",", instparams))



#LTLSPECS
#FIXME:
# Ojo con esta definicion, ya que puede contener inconsistencias debido a que
# no estoy seguro de que el orden entre LTLBOP y LTLUOP descarte el hecho de que
# vaya a dar correcto el matching con LTLBOP cuando en realidad sea una LTLUOP

ltlbinops = re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
ltluops = re.compile(r"\!|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")

def LTLSPEC():      return [(keyword("LTLSPEC"), LTLEXP) , (keyword("LTLSPECNAME"), IDENT, ":=", LTLEXP)]
def LTLEXP():       return [LTLBOP, LTLUOP]
def LTLBOP():       return LTLUOP , ltlbinops, LTLEXP
def LTLUOP():       return -1 , ltluops, LTLVAL
def LTLVAL():       return [ PROPFORM , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) ]



#FAIRNESS
def FAIRNESS():     return keyword("FAIRNESS"), PROPFORM
def COMPASSION():   return keyword("COMPASSION"), "(", PROPFORM, ",", PROPFORM, ")"


#COMENT
def COMMENT():      return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]



#///////////////////////////////////////////////////////////////////////////////



#\\\\\\\\\\\\\\\\\\\\\\\\BaSurA\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

"""
#LTL SPECIFICATIONS
def LTLSPEC():      return [ (keyword("LTLSPEC"), LTLEXP), (keyword("LTLSPEC NAME"), ":=", LTLEXP)]
def LTLEXP():       return [ LTLVAL, (LTLUOP, LTLEXP), (LTLVAL, LTLBOP, LTLVAL)]
def LTLVAL():       return [ (LTLUOP, LTLEXP), PROPFORM, (re.compile(r"\("), LTLEXP, re.compile(r"\)"))]
def LTLUOP():       return re.compile(r"\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")
def LTLBOP():       return re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")
"""
"""
###
def LTLSPEC():      return (keyword("LTLSPEC"), LTLEXP)
def LTLEXP():       return LTLVAL , -1 , ( ltlbinops, LTLVAL )
def LTLVAL():       return -1 , ltluops, [PROPFORM , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) ]
###
"""


""" @@@@ VERSION "TEORICAMENTE CORRECTA" @@@@

def LTLSPEC():      return (keyword("LTLSPEC"), LTLEXP)
def LTLEXP():       return LTLBOP
def LTLBOP():       return LTLUOP , -1 , ( ltlbinops, LTLUOP )
def LTLUOP():       return -1 , ltluops, LTLVAL
def LTLVAL():       return [PROPFORM , ("(" , LTLEXP, ")") ]

"""

"""
mathbinop = r"\+|\-|\*|\/|\%"
def MATH():         return [MATHBINOP , MATHUOP]
def MATHUOP():      return -1, re.compile(r"\-"), MATHVAL
def MATHBINOP():    return MATHUOP, re.compile(mathbinop), MATH
def MATHVAL():      return [ INT, IDENT, (re.compile(r"("), MATH, re.compile(r")"))]
"""

