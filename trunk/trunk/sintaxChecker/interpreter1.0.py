import re, fileinput
from pyPEG.pyPEG import parse
from pyPEG.pyPEG import keyword, _and, _not


#---- TODO ---------------------------------------------------------------------
#
#   1-  Se debe permitir formulas como (a->b)=(c->d) o se cubren con 
#       (a->b)<->(c->d)?
#
#   2-  Se puede hacer next(v) = next(v2)?
#
#   3-  Esta bien declarar fallas sin condicion de habilitacion ni efecto?
#
#   4-  Se puede tener mas de una accion con el mismo nombre en el mismo modulo?
#
#   5-  Revisar si next(v) = 0..6 es como next(v) = {0,1,2,3,4,5,6}
#
#---- END TODO -----------------------------------------------------------------


# VALIDAS PARA EL ENCABEZADO DEL MODULO ----------------------------------------
# - MODULE m()
# - MODULE m(;)
# - MODULE m(v1,v2,v3)
# - MODULE m(;a1,a2,a3)
# - MODULE m(v1,v2,v3;)
# ------------------------------------------------------------------------------


#------ LENGUAJE ---------------------------------------------------------------

#IDENTIFIERS

def IDENT():        return re.compile(r"(?!\bFAIRNESS\b|\bCOMPASSION\b|\bU\b|\bV\b|\bS\b|\bT\b|\bxor\b|\bxnor\b|\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b|\bnext\b|\bINSTANCE\b|\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*(\.[a-zA-Z_]+\w*)?")
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
def COMPOP():       return re.compile(r"\<(?!->)|\>|\=")
def NEXTPROPFORM(): return NEXTVAL, "=", [ SET, NEXTVAL, INT, PROPFORM], -1, ( ",", NEXTVAL, "=", [ INT, PROPFORM, NEXTVAL, SET])
def NEXTVAL():      return keyword("next"), "(", IDENT, ")"

#SYSTEM

def SYSTEM():       return -1, [MODULE, INSTANCE, LTLSPEC, FAIRNESS, COMPASSION]

#MODULE 

def MODULE():       return keyword("MODULE"), IDENT, "(", CONTEXTVARS, CONTEXTACTS, ")", MODULEBODY
def CONTEXTVARS():  return 0, (IDENT, -1, (",", IDENT))
def CONTEXTACTS():  return 0, (";", 0, ( IDENT, -1, (",", IDENT)))
def MODULEBODY():   return 0, VAR, 0, FAULT, 0, INIT, 0, TRANS
def VAR():          return keyword("VAR"), -1, VARDCL
def VARDCL():       return IDENT, ":", VARTYPE
def VARTYPE():      return [BOOLEAN,SET,RANGE]
def BOOLEAN():      return "bool"
def SET():          return "{", [IDENT, INT], -1, (",", [IDENT, INT]), "}"      #En NuSMV enumeration types no se pueden usar las palabras reservadas
def RANGE():        return re.compile(r"\d+"), "..", re.compile(r"\d+")

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


#LTL SPECIFICATIONS
def LTLSPEC():      return [ (keyword("LTLSPEC"), LTLEXP), (keyword("LTLSPEC NAME"), ":=", LTLEXP)]
def LTLEXP():       return [ (re.compile(r"\!"), LTLEXP), (LTLVAL, -1, (LTLBOP, LTLVAL))]
def LTLVAL():       return [ (LTLUOP, LTLEXP), PROPFORM, (re.compile(r"\("), LTLEXP, re.compile(r"\)"))]
def LTLUOP():       return re.compile(r"\bG\b|\bX\b|\bF\b|\bH\b|\bO\b|\bZ\b|\bY\b")
def LTLBOP():       return re.compile(r"\bU\b|\bV\b|\bS\b|\bT\b|xor|\||\<\-\>|\-\>|xnor|\&")


#FAIRNESS
def FAIRNESS():     return keyword("FAIRNESS"), PROPFORM
def COMPASSION():   return keyword("COMPASSION"), "(", PROPFORM, ",", PROPFORM, ")"


#----- END LENGUAJE ------------------------------------------------------------



files = fileinput.input()
result = parse(SYSTEM(), files, True)
print result







#def BOOL(): return re.compile(r"FALSE|TRUE")
#def MATHOPER():     return re.compile(r"[\+\-\*\/\%]")
#def COMPOPER():     return re.compile(r"\<(?!->)|\>|\=")#(r"\<|\>|\=|\>\=|\<\=")
#def LOGICOPER():    return re.compile(r"\-\>|\<\-|\<\-\>|\&|\||\=")
#def FORM():         return 0, re.compile(r"\-"), [IDENT,INT,(re.compile(r"\("), FORM, re.compile(r"\)"))], 0, ( MATHOPER, FORM)
#def COMPFORM():     return [FORM , BOOL] , COMPOPER, [FORM , BOOL]
#def PROPFORM():     return 0, re.compile(r"\!"), [COMPFORM, BOOL, IDENT, (re.compile(r"\("), PROPFORM, re.compile(r"\)"))], 0, (LOGICOPER, PROPFORM)
#[COMPFORM, IDENT, BOOL, (re.compile(r"\!"), PROPFORM)]


#def NEXTPROPFORM(): return [ (re.compile(r"\!(?!\=)"), NEXTPROPFORM), (NEXTPROPVAL, -1, ( LOGICOP, NEXTPROPVAL))]
#def NEXTPROPVAL():  return [ (re.compile(r"next"), "(", IDENT, ")", "=", [MATH, PROPFORM, SET]), (re.compile(r"\("), NEXTPROPFORM, re.compile(r"\)"))]

