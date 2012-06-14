# Test de todo el programa
# 14 de Junio de 2012
# Autor: Raul Monti

import sys, os

sys.path.append(os.path.abspath("../"))

import fileinput
from Compiler.Compiler import *
from Compiler.NamespaceChecker import * 
import Debug, Config
from Exceptions.Exceptions import *
from InputManager.Interpreter import *
from InputManager.Parser import *

if __name__ == '__main__':
    p = Parser()
    i = Interpreter()
    f = fileinput.input()
    par = p.parse(i.interpret(f))
    
    n = NamespaceChecker(par)
    n.checkAllNamespace()
    
    c = Compiler(par, 'out.smv')
    c.compile()
