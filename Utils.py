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
    return string


################################################################################

def putParenthesis(AST):
    """
        Devuelve un string con los elementos unicode de AST, colocando ademas
        parentesis segun presedencia de operadores. AST debe haber sido parseado
        por la regla EXPRESION de la gramatica de entrada de Falluto.
    """
    if isinstance(AST, Symbol):
        if len(AST.what) == 3:
            if AST.what[0] == "(":
                return putParenthesis(AST.what[1])
            else:
                return "(" + putParenthesis(AST.what[0]) + " " + AST.what[1] \
                     + " " + putParenthesis(AST.what[2]) + ")"
        elif len(AST.what) == 1:
            return putParenthesis(AST.what[0])
        elif len(AST.what) == 2:
            return AST.what[0] + putParenthesis(AST.what[1])
        else:
            Debug.WARNING("Passing through: " + repr(AST) + "\n")
            return _str(AST)
    elif isinstance(AST, unicode):
        return AST
    else:
        raise TypeError(AST)
   
