
from subprocess import call
import sys, os

from pyPEG.pyPEG import *
from src.GrammarRules2 import SYSTEM, COMMENT
from src.Parser2 import *
from src.Compiler2 import Compiler
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
    outputfile = c.compile(sys, "outcompilertest.smv")
    #Call NuSMV in a subprocess
    call(["NuSMV", os.path.abspath(outputfile)]) 
