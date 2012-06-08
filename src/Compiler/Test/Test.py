# NamespaceChecker test module

import sys, os, fileinput

sys.path.append(os.path.abspath('../../'))

from Compiler.NamespaceChecker import *
from InputManager import Interpreter
from InputManager import Parser

if __name__ == '__main__':
    parser = Parser.Parser()
    interpreter = Interpreter.Interpreter()
    checker = NamespaceChecker()
    files = fileinput.input()
    ast = interpreter.interpret(files)
    par = parser.parse(ast)
    try:
        checker.checkAllNamespace(par)
    except RedeclaredError, E:
        print "___@@@ Mensaje de error del modulo NamespaceChecker.py @@@___"
        print unicode(E)
