import sys, os
sys.path.append(os.path.abspath('../../'))


from GrammarRules2 import SYSTEM, COMMENT
from InputManager.pyPEG.pyPEG import *
import fileinput
import Debug
import Config

if __name__ == '__main__':

    files = fileinput.input()
    ast = parse(SYSTEM(), files, True, COMMENT, packrat = True,lineCount = True)
    Debug.debugYELLOW( ast)
