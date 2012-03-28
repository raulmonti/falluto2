import re, fileinput
from pyPEG.pyPEG import parse
from pyPEG.pyPEG import keyword, _and, _not


#

#IDENTIFIERS
def ident(): return re.compile(r"(?!\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*") #|\b\b
def typeidentifier():   return [bool, set, int]                                     #[re.compile(r"\d+\.\.\d+|\w+"), settype]
                                                                                    #re.compile(r"\d+\.\.\d+|\w+|\{\w+(, \w+)*\}")
#DATA TYPES
def bool():             return "bool"                                                                                  
def set():              return "{", identifier, -1, (",", identifier), "}"          #NO PUEDE SER DOMINO VACIO
def int():              return re.compile(r"\d+"), "..", re.compile(r"\d+")

#EXPRESIONS
def simple_expr():      return [identifier,
                               (re.compile(r"\-"), simple_expr)]
                              # (simple_expr, re.compile(r"\+"), simple_expr),
                              # (simple_expr, re.compile(r"\-"), simple_expr),
                              # (simple_expr, re.compile(r"\*"), simple_expr)]
                                
def next_expr():        return "NEXT"
                                
#SYSTEM
def system():           return -1, module                                

#MODULE HEADER
def module():           return keyword("module"), identifier, "(", varparamlist, actparamlist,  ")", modulebody
def varparamlist():     return 0, ( identifier, -1, (",", identifier))
def actparamlist():     return 0, ( ";", identifier, -1, (",", identifier))

#MODULE BODY
def modulebody():       return vardeclaration, initdeclaration, transdeclaration
def vardeclaration():   return "VAR", -1, (identifier, ":" , typeidentifier, ";")
def initdeclaration():  return "INIT", 0, simple_expr
def transdeclaration(): return "TRANS"

files = fileinput.input()
result = parse(system(), files, True)
print result


#PREGUNTAS
# 1- Esta bien corroborar en esta etapa si las expresiones escritas en INIT y 
#  - TRANS son booleanas o no? 
#
# 2- Esta bien en esta etapa corroborar que los tipos de datos escritos en INIT
#  - existan?
#
# 3- Estaria bien dar un limite de digitos para el caso de los enteros?
#




#DEPRECATED
#def identifierlist():   return 0, ( identifier, -1, (",", identifier))


