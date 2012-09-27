import sys, os, fileinput
#sys.path.append(os.path.abspath('../'))

from pyPEG import parse
from SyntaxRules import SYNTAX, COMMENT
from Parser import FallutoSystem
from Typing import *



"""~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"""


if __name__ == "__main__":

    _file = fileinput.input()
    _ast  = parse(SYNTAX, _file, True, COMMENT)

    print "Interpreted:\n\n", _ast

    sys = FallutoSystem()
    sys.parse(_ast)
    print sys
    
    typechecker = SysTypeCheck(sys)
    typechecker.check()
    
    print "ENDING"    
    




