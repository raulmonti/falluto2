"""
    Raul Monti 30 agosto 2012
    
    Modulo encargado de interpretar las trazas devueltas por NuSMV a partir del
    archivo generado por Falluto.
    
"""


import InputManager.pyPEG
from InputManager.pyPEG.pyPEG import keyword, _and, _not, ignore
import re
from Debug import *
from Config import *




#===============================================================================
class SpecificationResult():

    def __init__(self):
        self.specification = ""
        self.result = false
        self.trace = []
        
    def parse(self, ast):
        pass
        




#===============================================================================        
""" For printig whith colors :D 
    Put CR|CB|CG|CY before the text you want to color, and CE after it.
"""

CS = '\033['
CE = '\033[1;m'
CR = CS + '1;31m' #red start printing
CB = CS + '1;94m' #blue start printing
CG = CS + '1;32m' #green start printing
CY = CS + '1;33m' #yellow start printing




#===============================================================================        
class TraceInterpreter():
    
    def __init__(self):
        pass
        
    def interpret(self, ast):
    
        print CB + "\nHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH"\
                 + "HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH\nFaLLuTO "\
                 + "2 . 0 : 31 Agosto 2012\n\n" + CE
    
    
        for sp in ast:
            if sp.__name__ == "TRUESPEC":
                print CG + "|+|\tSpecification " + CE + CY + str(sp.what[0]) \
                    + CE + CG  + "is true\n\n" + CE


            if sp.__name__ == "FALSESPEC":
                print CR + "|-|\tSpecification " + CE + CY + str(sp.what[0]) \
                    + CE + CR  + "is false\n\n" + CE
                debugTODO("Interpret the trace Counterexample given here")
    
    


#===============================================================================
"""
    Lenguaje PyPEG para interpretar las trazas
"""

def SYS():          return -1, ignore(r"(?!--).*\n"), -1, [TRUESPEC, FALSESPEC]
def TRUESPEC():     return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("true")
def FALSESPEC():    return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("false"), TRACE
def TRACE():        return -1, ignore(r"(?!->).*\n"), -1 , STATE, -1, STATELOOP
def STATE():        return "->", "State:", re.compile(r"\d\.\d"), "<-", -1 , VARCHANGE
def VARCHANGE():    return re.compile(r"[a-zA-Z0-9\#\_]*"), "=", re.compile(r"[a-zA-Z0-9\#\_]*")
def STATELOOP():    return "--", "Loop", "starts", "here", -1, STATE



debugURGENT("Averiguar que significa que haya dos Loop starts here uno desp del "\
        + "otro, como en el caso de abajo")
"""
-- specification  G inst1#var1 != TRUE  is false
-- as demonstrated by the following execution sequence
Trace Description: LTL Counterexample 
Trace Type: Counterexample 
-> State: 2.1 <-
  action# = inst1#f2
  inst1#f1#active = FALSE
  inst1#f2#active = FALSE
  inst1#var1 = TRUE
-- Loop starts here
-> State: 2.2 <-
  action# = dk#action
-> State: 2.3 <-
  action# = inst1#f1
-- Loop starts here
-> State: 2.4 <-
  action# = dk#action
-> State: 2.5 <-
  action# = inst1#f1
-> State: 2.6 <-
  action# = dk#action
"""


