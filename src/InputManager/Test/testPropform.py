import sys, os
sys.path.append(os.path.abspath('../../'))


from GrammarRules2 import SYSTEM, COMMENT, PROPFORM
from InputManager.pyPEG.pyPEG import *
import fileinput
import Debug
import Config

if __name__ == '__main__':

    files = fileinput.input()
    ast = parse(PROPFORM(), files, True, COMMENT, lineCount = True)
    Debug.DebugYELLOW( ast)
