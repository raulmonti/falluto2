import sys, os
sys.path.append(os.path.abspath('../../'))


from GrammarRules2 import SYSTEM, COMMENT
from Parser2 import *
from InputManager.pyPEG.pyPEG import *
from Compiler2 import Compiler
import fileinput
import Debug
import Config

if __name__ == '__main__':

    files = fileinput.input()
    ast = parse(SYSTEM(), files, True, COMMENT, lineCount = True)
    #Debug.DebugYELLOW( ast)
    sys = System()
    sys.parse(ast)
    #sys.printMe()
    c = Compiler()
    c.compile(sys, "outcompilertest.smv")
