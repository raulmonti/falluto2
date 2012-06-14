# NamespaceChecker test module

import sys, os, fileinput

sys.path.append(os.path.abspath('../../'))

from Compiler.NamespaceChecker import *
from InputManager import Interpreter
from InputManager import Parser
import Config

if __name__ == '__main__':
    parser = Parser.Parser()
    interpreter = Interpreter.Interpreter()    
    _files = fileinput.input()
    
    _ast = interpreter.interpret(_files)
    _par = parser.parse(_ast)
    checker = NamespaceChecker(_par)
    try:
        checker.checkAllNamespace()
    except RedeclaredError, E:
        print "___@@@ Mensaje de error del modulo NamespaceChecker.py @@@___"
        print unicode(E)
