import re, fileinput
from pyPEG import parse
from pyPEG import keyword, _and, _not

def comment():          return [re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]
def literal():          return re.compile(r'\d*\.\d*|\d+|".*?"')
def symbol():           return re.compile(r"\w+")
def operator():         return re.compile(r"\+|\-|\*|\/|\=\=")
def operation():        return symbol, operator, [literal, functioncall]
def expression():       return [literal, operation, functioncall]
def expressionlist():   return expression, -1, (",", expression)
def returnstatement():  return keyword("return"), expression
def ifstatement():      return keyword("if"), "(", expression, ")", block, keyword("else"), block
def statement():        return [ifstatement, returnstatement], ";"
def block():            return "{", -2, statement, "}"
def parameterlist():    return "(", symbol, -1, (",", symbol), ")"
def functioncall():     return symbol, "(", expressionlist, ")"
def function():         return keyword("function"), symbol, parameterlist, block #re.compile("function"), symbol, parameterlist, block
def simpleLanguage():   return -1, function


files = fileinput.input()
result = parse(simpleLanguage(), files, True, comment)
print result
