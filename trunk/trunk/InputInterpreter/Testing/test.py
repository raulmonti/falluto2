#Testing module for inputInterpreter modules

import sys, os
sys.path.append(sys.path[0])
sys.path[0] = (os.path.abspath('../'))

import interpreter
import parser
import fileinput


if __name__ == '__main__':

    files = fileinput.input()

    interpreter = interpreter.Interpreter()
    interpreterResult = interpreter.interpret(files)
    
    print "\n\n********** INTERPRETER RESULT **********\n\n"
    print interpreterResult
    
   
    par = parser.Parser()
    parserResult = par.parse(interpreterResult)
    
    print "\n\n********** PARSER RESULT **********\n\n"
    parserResult.printMe()
