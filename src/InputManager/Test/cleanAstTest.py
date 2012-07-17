# Test de InputManager

import sys, os

sys.path.append(os.path.abspath('../../'))

from InputManager import Parser, Interpreter
import fileinput

if __name__ == '__main__':
    parser = Parser.Parser()
    interpreter = Interpreter.Interpreter()
    files = fileinput.input()
    ast = interpreter.interpret(files)
    for x in ast:
        if x.__name__ == 'LTLSPEC':
            print x.what
            print "CLEANED"
            cleaned = parser.cleanAST(x)
            print cleaned
            for x in cleaned:
                print x,
            
    print "\n\n\n"    
    parser.parse(ast).printMe()
