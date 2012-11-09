import pyPEG
from pyPEG import Symbol
import Debug

################################################################################

def _cl(ast = []):
    """
        Devuelve una lista formada por los elementos de tipo unicode que estan 
        dentro del AST. 'ast' debe haber sido contruido por la funcion parse o 
        parseLine del modulo pyPEG o debe ser una subseccion del mismo, siempre y 
        cuando sea de tipo Symbol, list o unicode.
    """
    ret = []
    if isinstance(ast, pyPEG.Symbol):
        ret += _cl(ast.what)
    elif isinstance(ast, unicode) or isinstance(ast, str):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += _cl(x)
    elif ast == None:
        pass
    else:
        raise Exception("Not AST type: " + str(ast))

    return ret



################################################################################

def _str(ast = []):
    """
        Devuelve un string formado por los elementos de tipo unicode que estan 
        dentro del AST separados entre ellos por espacios simples. 'ast' debe 
        haber sido contruido por la funcion parse o parseLine del modulo pyPEG 
        o debe ser una subseccion del mismo, siempre y cuando sea de tipo 
        Symbol, list o unicode.
    """
    lst = _cl(ast)
    string = ""
    if lst != []:
        string = str(lst[0])
    for element in lst[1::]:
        string += " " + str(element)
    return str(string)


################################################################################

def putBrackets(AST):
    """
        Devuelve un string con los elementos unicode de AST, colocando ademas
        parentesis segun presedencia de operadores. AST debe haber sido parseado
        por la regla EXPRESION de la gramatica de entrada de Falluto.
    """
    if isinstance(AST, Symbol):
        if len(AST.what) == 3:
            if AST.what[0] == "(":
                return putBrackets(AST.what[1])
            else:
                return "(" + putBrackets(AST.what[0]) + " " + _str(AST.what[1])\
                     + " " + putBrackets(AST.what[2]) + ")"
        elif len(AST.what) == 1:
            return putBrackets(AST.what[0])
        elif len(AST.what) == 2:
            return AST.what[0] + putBrackets(AST.what[1])
        else:
            Debug.WARNING("Passing through: " + repr(AST) + "\n")
            return _str(AST)
    elif isinstance(AST, unicode) or isinstance(AST, str):
        return AST
    else:
        raise TypeError(AST)


################################################################################

def putBracketsToFormula(AST):
    """
        Devuelve un string con los elementos unicode de AST, colocando ademas
        parentesis segun presedencia de operadores a los subAST de tipo 
        EXPRESION que se encuentren dentro de AST.
    """
    if isinstance(AST, Symbol):
        if AST.__name__ == "EXPRESION":
            return putBrackets(AST) + ' '
        else:
            string = ""
            for elem in AST.what:
                string += putBracketsToFormula(elem)
            return string
    elif isinstance(AST, unicode) or isinstance(AST, str):
        return AST + ' '
    else:
        raise TypeError(AST)

################################################################################
def isBool(var):
    return var == "TRUE" or var == "FALSE"


################################################################################

def isInt(var):
    try:
        int(var)
        return True
    except ValueError:
        return False

################################################################################
__bigLineNumber = "Can't find out line number. Check first and last line of your falluto system specification."

def lineMin(line1, line2):
    """
        Return the minimum between two pyPEG line numbers (of the form
        'file:#'.
    """
    if not ':' in line1: # or line1 = __bigLineNumber: (__bigLineNumber hasn't ':')
        return line2
    if not ':' in line2: #or line2 = __bigLineNumber:
        return line1
    assert ':' in line1 and ':' in line2
    int1 = int(line1.split(':',1)[1])
    int2 = int(line2.split(':',1)[1])
    if int1 < int2:
        return line1
    else:
        return line2
    
    
def getBestLineNumberForExpresion(expr):
    """
        The minimum line number in the expresion is usually the best option 
        for the expresion's line.
    """
    line = __bigLineNumber
    if isinstance(expr, unicode):
        return __bigLineNumber
    elif isinstance(expr, pyPEG.Symbol):
        line = expr.__name__.line
        line = lineMin( line, getBestLineNumberForExpresion( expr.what))
        return line
    elif isinstance(expr, list):
        for elem in expr:
            line = lineMin(line, getBestLineNumberForExpresion( elem))
            return line
    else:
        raise TypeError(expr)
        
################################################################################

__expresion = "EXPRESION" # name of the Expresions Symbols in the actual grammar

def getExpresions(formula):
    """
        Get a list with the '__expresion' named pyPEG.Symbol objects found inside
        'formula'.
    """
    result = []
    if isinstance(formula, pyPEG.Symbol):
        if formula.__name__ == __expresion:
            result.append(formula)
        else:
            result += getExpresions(formula.what)
    elif isinstance(formula, list):
        for elem in formula:
            result += getExpresions(elem)
    elif isinstance(formula, unicode):
        return []
    else:
        raise TypeError(formula)
    return result
################################################################################

class TabLevel():
    """
        Para definir el nivel de tabulado a partir del cual imprimir el output.
        Para agregar n '\t's al tabulado hacemos Tablevel += n. Similarmente 
        para restar hacemos -= n. str(Tablevel) devuelve el string con la
        cantidad de \t elegidos.
    """
    def __init__(self):
        self.level = 0

    def __str__(self):
        string = ""
        for x in range(0,self.level):
            string += '\t'
        return string

    def __add__(self, other):
        if type(other) == int :
            self.level += other
            return self
        else:
            raise TypeError

    def __sub__(self, other):
        if type(other) == int :
            self.level -= other
            return self
        else:
            raise TypeError

    def reset(self):
        self.level = 0

    def i(self):
        self.level += 1

    def d(self):
        self.level -= 1

################################################################################

