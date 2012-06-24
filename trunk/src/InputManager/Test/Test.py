# Test de InputManager

import sys, os

sys.path.append(os.path.abspath('../../'))

from InputManager import Parser, Interpreter
import fileinput
from Debug import *
from Config import *

if __name__ == '__main__':
    parser = Parser.Parser()
    interpreter = Interpreter.Interpreter()
    files = fileinput.input()
    ast = interpreter.interpret(files)
    DebugYELLOW(ast)
    for x in ast:
        if x.__name__ == 'LTLSPEC':
            print x.what
    print "\n\n\n"    
    parser.parse(ast).printMe()
