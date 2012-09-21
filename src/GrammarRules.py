#===============================================================================
# Modulo GrammarRules.py
# 7 de Junio del 2012
# Autor: Raul Monti
# F A L L U T O    2 . 0
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

# OPTIONS HEADER MAP ############
"""                             #
OPTIONS                         
                                
--FLLNAME outputname            
--CHECK_DEADLOCK                
--FAULT_SYS_FAIR_DISABLE        
--MODULE_WEAK_FAIR_DISABLE      
                                
ENDOPTIONS                      
"""                             #
#################################


debugURGENT("Usar CTL en vez de LTL ya que es mucho mas rapido de chequear")


debugTODO("Revisar todo este modulo, packrat por se clava con la ltlspec"  \
           + " G ( just(w) -> X ((just(r) -> X (sys.value = sys.output)) " \
           + "U just(w))).")
debugTODO("Definir todo esto de nuevo, si o si primero en hoja :S")

debugTODO("Lograr trazas de contraejemplo mas cortas y lindas :D")


#///////////////////////////////////////////////////////////////////////////////
#   LENGUAGE (EN PEG)
#


#===============================================================================

#IDENTIFIERS
identifiers = r"(?!\bin\b|\bCHECKDEADLOCK\b|\bENDOPTIONS\b|\bOPTIONS\b|\
\bFLLNAME\b|\bjust\b|\bis\b|\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\
\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bENDMODULE\b|\
\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\
\bFAULT\b)[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?"


def IDENT():        return re.compile(identifiers)
def INT():          return re.compile(r"\-?\d+")
def BOOL():         return re.compile(r"\bFALSE\b|\bTRUE\b")
def ACTION():       return "just(", re.compile(identifiers), ")"










#===============================================================================

#MATH FORMULA
# Los operadores anidan a derecha, no doy prioridades ya que no vienen al caso
# despues que se las arregle NuSMV o quien sea. 
mathbinop = r"\+|\-|\*|\/|\%"
def MATH():         return [MATHBINOP, MATHVAL]
def MATHBINOP():    return MATHVAL , re.compile(mathbinop), MATH
def MATHVAL():      return [ INT, IDENT, (re.compile(r"\("), MATH, \
                            re.compile(r"\)")), (re.compile(r"\-"), MATH)]








#===============================================================================
#SET INCLUSION
def INCLUSION(): return [(IDENT, "'"),IDENT], re.compile(r"in"), \
                        [(re.compile(r"{"), IDENT, -1, \
                        (re.compile(r","), IDENT) , re.compile(r"}")), \
                        (INT, re.compile(r".."), INT)]









#===============================================================================
#BOOLEAN FORMULA
booleanop = r"\<\=|\>\=|\<(?!->)|\>|\=|\!\="
def BOOLEXP():      return [BOOLBINOP, BOOLVAL]
def BOOLBINOP():    return BOOLVAL, re.compile(booleanop), BOOLEXP
def BOOLVAL():      return [ BOOL, INCLUSION, MATH, IDENT, \
                            (re.compile(r"\("), BOOLEXP, re.compile(r"\)")), \
                            (re.compile(r"\!"), BOOLEXP)]










#===============================================================================
#PROPOSITIONAL FORMULA
propbinop = r"\-\>|\&|\||\<\-\>"
def PROPFORM():     return [PROPBINOP, PROPVAL]
def PROPBINOP():    return PROPVAL, re.compile(propbinop), PROPFORM
def PROPVAL():      return [BOOLEXP, (re.compile(r"\("), PROPFORM, \
                            re.compile(r"\)")), (re.compile(r"\!"), PROPFORM)]









#===============================================================================
#NEXT PROPOSITIONAL FORMULA
def NEXTPROPFORM(): return NEXTVAL, -1, ( ",", NEXTVAL)
def NEXTVAL():      return IDENT, "'", [( "=", \
                           [ PROPFORM, MATH, NEXTREF, IDENT, SET ]),("in", [SET, RANGE])]
def NEXTREF():      return IDENT, "'"



#VAR TYPES
def SET():          return "{", [IDENT, INT, BOOL], -1, (",", [IDENT, INT, BOOL]), "}"
def RANGE():        return INT, "..", INT
def BOOLEAN():      return "bool"


#SYSTEM
def SYSTEM():       return 0, OPTIONS , -1, [MODULE, INSTANCE, LTLSPEC, FAIRNESS, COMPASSION, PROPERTIE]



#===============================================================================
"""
    OPTIONS
"""
def OPTIONS():      return keyword("OPTIONS"), -1, [SYSNAME, CHECKDEADLOCK, FAULTSYSFAIRDISABLE, MODULEWFAIRDISABLE], \
                           keyword("ENDOPTIONS")
def SYSNAME():              return "FLLNAME", re.compile(r"[\w\.\d\_]*")
def CHECKDEADLOCK():        return keyword("CHECK_DEADLOCK")
def FAULTSYSFAIRDISABLE():  return keyword("FAULT_SYS_FAIR_DISABLE")
def MODULEWFAIRDISABLE():   return keyword("MODULE_WEAK_FAIR_DISABLE")





#===============================================================================
"""
    COMMON PROPERTIES TO BE CHECKED
"""
def PROPERTIE():        return [NORMALBEHAIVIOUR, FINMANYFAULTS, FINMANYFAULT]
def NORMALBEHAIVIOUR(): return keyword("NORMAL_BEHAIVIOUR"), "(", LTLEXP, ")"
def FINMANYFAULTS():    return keyword("FINITELY_MANY_FAULTS"), "(", LTLEXP, ")"
def FINMANYFAULT():     return keyword("FINITELY_MANY_FAULT"), "(", IDENT, -1, (",", IDENT), ";" ,LTLEXP, ")"
def NGOODTRANS():       return keyword("N_GOOD_TRANS"), "(", INT, ";", LTLEXP, ")"
#def NGOODTRANSF():      return keyword("N_GOOD_TRANS_F"), "(", INT, ";", IDENT, -1, (",", IDENT), ";", LTLEXP, ")"





#===============================================================================
"""
    MODULES
"""
def MODULE():       return keyword("MODULE"), IDENT, "(", CONTEXTVARS, \
                            CONTEXTACTS, ")", MODULEBODY, keyword("ENDMODULE")

def CONTEXTVARS():  return 0, (IDENT, -1, (",", IDENT))
def CONTEXTACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS

def VAR():          return keyword("VAR"), -1, VARDECL
def VARDECL():      return IDENT, ":", [ BOOLEAN, SET, RANGE]

def FAULT():        return keyword("FAULT"), -1, FAULTDECL
def FAULTDECL():    return IDENT, ":", 0, PROPFORM, 0, ("=>", NEXTPROPFORM), "is", FAULTTYPE

def INIT():         return keyword("INIT"), 0, PROPFORM

def TRANS():        return keyword("TRANS"), -1, TRANSDECL
def TRANSDECL():    return "[", 0, IDENT, "]", ":", 0, PROPFORM, 0, ("=>", NEXTPROPFORM)
def FAULTTYPE():    return [BIZ, STOP, TRANSIENT]
def BIZ():          return "BIZ", "(", IDENT, -1, (",", IDENT), ")"
def STOP():         return [("STOP", "(", IDENT, -1, (",", IDENT), ")"), "STOP"]
def TRANSIENT():    return "TRANSIENT"


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
def LTLVAL():       return [ EVENTPRED , (re.compile(r"\(") , LTLEXP, re.compile(r"\)")) ]


#LTL PROP FORMULA
def EVENTPRED():  return [EVENTPREDBINOP, EVENTPREDVAL]
def EVENTPREDBINOP(): return EVENTPREDVAL, re.compile(propbinop), EVENTPRED
def EVENTPREDVAL():   return [ ACTION, BOOLEXP, \
                             (re.compile(r"\("), EVENTPRED, re.compile(r"\)")),\
                             (re.compile(r"\!"), EVENTPRED)]


#FAIRNESS
def FAIRNESS():     return keyword("FAIRNESS"), EVENTPRED
def COMPASSION():   return keyword("COMPASSION"), "(", EVENTPRED, ",", EVENTPRED, ")"

#COMENT
def COMMENT():      return [re.compile(r"--.*"), re.compile("/\*.*?\*/", re.S)]



