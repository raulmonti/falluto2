# test new grammar rules
import sys, os
sys.path.append(os.path.abspath('../../'))
from InputManager.pyPEG.pyPEG import parseLine
import fileinput
from GrammarRules2 import *
from Debug import *
from Config import *


class Tester():
    def __init__(self):
        self.string = ""
        self.error = ""
        self.runningTest = ""
        self.grammar = None
    
    def testOK(self):
        match = ""
        notmatch = ""
        try:
            match, notmatch = parseLine(self.string, self.grammar, [], True, COMMENT)
            if notmatch != "":
                DebugRED( self.error + " running test " + self.runningTest +\
                          "No Matching for \'" + notmatch)
            else:
                DebugGREEN( self.runningTest + " OK!!  ....   " + self.string ) 
        except SyntaxError , E:
            DebugRED( self.error + " running test " + self.runningTest + " SyntaxError rised trying to parse: \'" + self.string + "\'")
        


    def testMATH(self):
        self.error = "GRRR TestMath went RONG!"
        self.grammar = MATH()
        # 1
        self.runningTest = "MATH # 1"
        self.string = "1"
        self.testOK()        
        # 2
        self.runningTest = "MATH # 2"
        self.string = "(((4 + 1) / -1) * x + y) - (4+a * y)"
        self.testOK()


    def testBOOLEXP(self):
        self.error = "GRRR testBoolexp went RONG!"
        self.grammar = BOOLEXP()
        # 1
        self.runningTest = "BOOLEXP # 1"
        self.string = "(((4 + 1) / -1) * x + y) - (4+a * y) > 3 != FALSE"
        self.testOK()        


    def testPROPFORM(self):
        self.error = "GRRR testPROPFORM went RONG!"
        self.grammar = PROPFORM()
        # 1
        self.runningTest = "PROPFORM # 1"
        self.string = "TRUE & FALSE"
        self.testOK()
        # 2
        self.runningTest = "PROPFORM # 2"
        self.string = "TRUE & FALSE & !a != FALSE"
        self.testOK()
        # 3
        self.runningTest = "PROPFORM # 3"
        self.string = "4 > 2 & TRUE -> (9*a > 2) | x"
        self.testOK()

    def testNEXTPROPFORM(self):
        self.error = "GRRR testNEXTPROPFORM went RONG!"
        self.grammar = NEXTPROPFORM()
        # 1
        self.runningTest = "NEXTPROPFORM # 1"
        self.string = "next(a) = TRUE | FALSE"
        self.testOK()




if __name__ == '__main__':
    tester = Tester()
    tester.testMATH()
    tester.testPROPFORM()
    tester.testBOOLEXP()
    tester.testNEXTPROPFORM()
