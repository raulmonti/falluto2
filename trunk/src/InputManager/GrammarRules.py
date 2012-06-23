#===============================================================================
# Modulo GrammarRules.py
# 7 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

"""
    En este modulo se determinan las reglas gramaticales que definen la 
    gramatica de entrada para falluto. Las reglas seran interpretadas por los 
    modulos de la libreria PyPEG.
"""

import pyPEG
from pyPEG.pyPEG import keyword, _and, _not
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

# Agregamos a la siguiente lista separada por '|' las palabras que no queremos 
# que sean reservadas para el programa, y por lo tanto no queremos permitir como 
# identificadores.
identifiers = re.compile(r"(?!\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bnext\b|\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?")


#IDENTIFIERS

def IDENT():        return identifiers
def INT():          return re.compile(r"\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")

#FORMULAS

def PROPFORM():     return [ (re.compile(r"\!(?!\=)"), PROPFORM), (PROPVAL, -1, ( LOGICOP, PROPVAL))]
def PROPVAL():      return [ COMP, BOOL, IDENT, (re.compile(r"\("), PROPFORM, re.compile(r"\)"))]
def LOGICOP():      return re.compile(r"\-\>|\&|\||\<\-\>")
def COMP():         return MATH, COMPOP, MATH
def MATH():         return [ (re.compile(r"\-(?!>)"), MATH), (MATHVAL, -1, (MATHOP, MATHVAL))]
def MATHVAL():      return [ BOOL, IDENT, INT, SET, (re.compile(r"\("), MATH, re.compile(r"\)"))]
def MATHOP():       return re.compile(r"\+|\-|\*|\/|\%")
def COMPOP():       return re.compile(r"\<\=|\>\=|\<(?!->)|\>|\=")
def NEXTPROPFORM(): return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return keyword("next"), "(", IDENT, ")", "=", [SET, NEXTVAL, MATH, PROPFORM, INT]

#SYSTEM

def SYSTEM():       return -1, [MODULE, INSTANCE, LTLSPEC, FAIRNESS, COMPASSION]

#MODULE

def MODULE():       return keyword("MODULE"), IDENT, "(", CONTEXTVARS, CONTEXTACTS, ")", MODULEBODY
def CONTEXTVARS():  return 0, (IDENT, -1, (",", IDENT))
def CONTEXTACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS
def VAR():          return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, ":", [BOOLEAN,SET,RANGE]
def BOOLEAN():      return "bool"
DebugYELLOW("Porblema con los SET que se estan parseando mal :(\n")
def SET():          return "{", [IDENT, INT], -1, (",", [IDENT, INT]), "}"      #En NuSMV enumeration types no se pueden usar las palabras reservadas
def RANGE():        return INT, "..", INT

def FAULT():        return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return IDENT, ":", 0, PROPFORM, ":", 0, NEXTPROPFORM

def INIT():         return keyword("INIT"), 0, PROPFORM
def TRANS():        return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":", 0, PROPFORM, ":", 0, NEXTPROPFORM, -1, PFAULTDECL
def PFAULTDECL():   return "..", [BIZ, STOP], ".."
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def STOP():         return "STOP"


#INSTANCE
def INSTANCE():     return keyword("INSTANCE"), IDENT, "=", IDENT, "(", PARAMLIST, ")"
def PARAMLIST():    return 0, (re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"), -1, ( ",", re.compile(r"[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?")))



#LTLSPECS#######################################################################
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

#------------------------------------------------------------------------------#




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




