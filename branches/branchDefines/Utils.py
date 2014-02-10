# Module Utils.py
# Author Raul
# Fri 31 Jan 2014 07:20:17 PM ART 


import pyPEG
from pyPEG import Symbol
import Debug
from Debug import *


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
# TODO remove next if not used
def ss(ast = [], sp = True):
    """
        Devuelve un string formado por los elementos de tipo unicode que estan 
        dentro del AST separados entre ellos por espacios (si 'sp'). 'ast' debe 
        haber sido contruido por la funcion parse o parseLine del modulo pyPEG 
        o debe ser una subseccion del mismo, siempre y cuando sea de tipo 
        Symbol, list o unicode.
    """
    spp = ""
    if sp:
        spp = " "
    lst = _cl(ast)
    string = ""
    if lst != []:
        string = str(lst[0])
    for element in lst[1::]:
        string += spp + str(element)
    return str(string)


################################################################################

def putBrackets(AST, space = True):
    """
        Devuelve un string con los elementos unicode de AST, colocando ademas
        parentesis segun presedencia de operadores. AST debe haber sido parseado
        por la regla EXPRESION de la gramatica de entrada de Falluto.
    """
    
    obrace = ' ( '
    cbrace = ' ) '
    if not space:
        obrace = '('
        cbrace = ')'
    if isinstance(AST, Symbol):
        if len(AST.what) == 3:
            if AST.what[0] == "(":
                return putBrackets(AST.what[1], space)
            else:
                return obrace + putBrackets(AST.what[0],space) + " " \
                     + ss(AST.what[1]) \
                     + " " + putBrackets(AST.what[2],space) + cbrace
        elif len(AST.what) == 1:
            return putBrackets(AST.what[0],space)
        elif len(AST.what) == 2:
            return AST.what[0] + " " + putBrackets(AST.what[1],space)
        else:
            Debug.debugWARNING("Passing through: " + repr(AST) + "\n")
            return ss(AST)
    elif isinstance(AST, unicode) or isinstance(AST, str):
        return AST
    else:
        raise TypeError(AST)

################################################################################

def putBracketsAsList(AST):
    return putBrackets(AST).split()

################################################################################

def putBracketsToFormula(AST, space=True):
    """
        Devuelve un string con los elementos unicode de AST, colocando ademas
        parentesis segun presedencia de operadores a los subAST de tipo 
        EXPRESION que se encuentren dentro de AST.
    """
    sp = ' '
    if not space:
        sp = ''
    if isinstance(AST, Symbol):
        if AST.__name__ == "EXPRESION":
            return putBrackets(AST,space) + sp
        else:
            string = ""
            for elem in AST.what:
                string += putBracketsToFormula(elem, space)
            return string
    elif isinstance(AST, unicode) or isinstance(AST, str):
        return AST + sp
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

__bigLineNumber = " Can't find out line number. Check first and last line of"\
                + " your falluto system specification."

def lineMin(line1, line2):
    """
        Return the minimum between two pyPEG line numbers (of the form
        'file:#'.
    """
    if not ':' in line1: #or line1 = __bigLineNumber: (__bigL... hasn't got ':')
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

################################################################################    
    
def getBestLineNumberForExpresion(expr):
    """
        The minimum line number in the expresion is usually the best option 
        for the expresion's line.
    """
    line = __bigLineNumber
    if isinstance(expr, unicode) or isinstance(expr, str):
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


# TODO remove next if not used.
################################################################################

#__expresion = "EXPRESION" # name of the Expresions Symbols in the actual grammar

#def getExpresions(formula):
#    """ Get a list with the '__expresion' named pyPEG.Symbol objects found 
#        inside 'formula'.
#    """
#    result = []
#    if isinstance(formula, pyPEG.Symbol):
#        if formula.__name__ == __expresion:
#            result.append(formula)
#        else:
#            result += getExpresions(formula.what)
#    elif isinstance(formula, list):
#        for elem in formula:
#            result += getExpresions(elem)
#    elif isinstance(formula, unicode):
#        return []
#    else:
#        raise TypeError(formula)
#    return result

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

    def _ss__(self):
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

def symbolSeparatedTupleString(array, parent = False, enter=False, tl="", \
                                 symb = '&'):
    parentopen = ""
    parentclose = ""
    amperson = " " + symb + " "
    if parent:
        parentopen = "("
        parentclose = ")"
    if enter:
        amperson = amperson + "\n" + tl

    marray = []
    for elem in array:
        if str(elem) != "":
            marray.append(elem)
    if marray == []:
        return ""
    elif len(marray) == 1:
        return str(marray[0])
    else:
        string = parentopen + "(" + str(marray[0]) + ")"
        for elem in marray[1::]:
            string += amperson + "(" + str(elem) + ")"
        string += parentclose
        return string
        
################################################################################
def commaSeparatedString(array, symb = ','):
    """ Get an array of elements, take them to string and return a string
        with them separated by commas.
    """
    result = ''
    for x in array[:-1]:
        result += str(x) + ', '
    result += str(array[-1])
    return result

################################################################################

def ast2str(ast=[], skipcomments=False, skipwhites=False):
    """ Take a pyAST and return a string with the parsed text in it.

        @input ast: the pyAST structure with the parsed text
        @input skipcomments: if don't want to compose the 'COMMENTS' from 'ast'
        @input skipwhites: if don't want to compose the 'BL' from 'ast'
        @return: a unicode string with the text parsed inside 'ast'
    """
    res = ""
    if isinstance( ast, unicode):
        res = ast
    elif isinstance(ast, pyPEG.Symbol):
        if ast.__name__ == u"COMMENT" and skipcomments:
            res = ""
        elif ast.__name__ == "BL" and skipwhites:
            res = ""
        else:
            res = ast2str(ast.what, skipcomments, skipwhites)
    elif isinstance(ast , list):
        for x in ast:
            res += ast2str(x, skipcomments, skipwhites)
    else:
        raise TypeError(str(ast))
    return unicode(res)

################################################################################

#def cleanAstOld(ast=[], cleanList=[]):
#    """ Take a pyAST and return a new one which is equal except for certain 
#        pySymbol elements that will be removed.
#
#        @input ast: the pyAST structure with the parsed text.
#        @input cleanList: list of pySymbol names (unicode attr __name__) to 
#                          remove.
#        @return: a new ast without the pySymbols with names from 'cleanList'.
#    """
#    _res = []
#    if isinstance( ast, unicode):
#        _res = ast
#    elif isinstance(ast, pyPEG.Symbol):
#        if ast.__name__ in cleanList:
#            _res = []
#        else:
#            _res = ast
#            _res.what = cleanAstOld(_res.what, cleanList)
#    elif isinstance(ast , list):
#        for _x in ast:
#            _r = cleanAstOld(_x, cleanList)
#            if _r != []:
#                # TODO may need extend instead of append?
#                _res.append(_x)
#    else:
#        raise TypeError(str(ast))
#    return _res


################################################################################

def cleanAst(ast=[], cleanList=[], level=-1, remUni=False):
    """ Take a pyAST and return a new one which is equal except for certain 
        pySymbol elements that will be removed.

        @input ast: the pyAST structure with the parsed text.
        @input cleanList: list of pySymbol names (unicode attr __name__) to 
                          remove.
        @input level: max level of recursion into PyPEG Symbol tree.
        @input remUni: remove unicodes aswell.
        @return: a new ast without the pySymbols with names from 'cleanList'.
    """
    _res = []
    if level == 0:
        _res = ast
    else:
        if isinstance( ast, unicode):
            if remUni:
                _res = []
            else:
                _res = ast
        elif isinstance(ast, pyPEG.Symbol):
            if ast.__name__ in cleanList:
                _res = []
            else:
                _res = ast
                _res.what = cleanAst(_res.what, cleanList, max(-1,level-1), remUni)
        elif isinstance(ast , list):
            for _x in ast:
                _r = cleanAst(_x, cleanList, level, remUni)
                if _r != []:
                    _res.append(_x)
        else:
            raise TypeError(str(ast))
    return _res


################################################################################

def clearAst(ast):
    """ Remove blanks and unicodes from first level of ast """
    return cleanAst(ast, cleanList=['BL'], level=1, remUni=True)

################################################################################

def getAst(ast=[], getList=[]):
    """ Something like the inverse of cleanAst, and puts everything into a list
        
        @input ast: the pyAST structure with the parsed text.
        @input getList: list of pySymbol names (unicode attr __name__) that 
                        you want to keep.
        @return: a list without the pySymbols with names not in 'getList'.
    """
    #TODO add level of depth to this function (look for the requested ast, until
    #     'depth' is reached in the tree of recursion.
    _res = []
    if isinstance( ast, unicode):
        _res = []
    elif isinstance(ast, pyPEG.Symbol):
        if ast.__name__ in getList:
            _res = ast
        else:
            _res = getAst(ast.what, getList)
    elif isinstance(ast , list):
        for _x in ast:
            _r = getAst(_x, getList)
            if _r != []:
                if isinstance(_r, pyPEG.Symbol):
                    _res.append(_r)
                elif isinstance(_r, list):
                    _res.extend(_r)
                else:
                    raise TypeError(str(_r))
    else:
        raise TypeError(str(ast))
    return _res
 #TODO clean module ( a lot of functions never used )
