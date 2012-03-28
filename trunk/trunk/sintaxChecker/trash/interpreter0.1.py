import re, fileinput
from pyPEG.pyPEG import parse
from pyPEG.pyPEG import keyword, _and, _not

#IDENTIFIERS

def ident(): return re.compile(r"(?!\bTRANS\b'|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*")

def system(): return -1, ident

files = fileinput.input()
result = parse(system(), files, True)
print result



#ANDAN:

#def ident(): return re.compile(r"(?!\bTRANS\b|\bINIT\b|\bVAR\b|\bMODULE\b|\bFALSE\b|\bTRUE\b|\bFAULT\b)[a-zA-Z_]+\w*")

#TODO
# 1- agregar palabras reservadas de NuSMV a las restricciones de ident.
