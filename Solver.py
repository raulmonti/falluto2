# MATH FORMULAS SOLVER FOR FALLUTO2.1
# Uses externals pyPEG and re
# Raul Monti
# 29/03/2014 01:05:05 
# Falluto2.1

from pyPEG import parseLine, Symbol
import re
from Utils import ast2str


# Parsing rules ================================================================
__rc = re.compile

def SUM():  return PROD, -1, (__rc(r'[\+\-]'), PROD)
def PROD(): return VAL, -1, (__rc(r'[\*\/\%]'), VAL)
def VAL():  return 0, __rc(r'\-'), [ __rc(r'\d+')
                                   , (__rc(r'\('), SUM, __rc('\)'))
                                   , NAME
                                   ]
def NAME(): return __rc(r"[a-zA-Z_]+\w*")


# Exceptions ===================================================================
class NotMath(Exception):
    def __init__(self, error):
        Exception.__init__(self)
        self.err = str(error) + " is not a math formula."
    def __str__(self):
        return self.err

class NoName(Exception):
    def __init__(self, error):
        Exception.__init__(self)
        self.err = "<" + str(error) + "> doesn't name a constant"\
                   + " value in the model."
    def __str__(self):
        return self.err

# The Solver Class =============================================================

class Solver():

    mainSolver = None # The main solver object.

    def __init__(self):
        self.defTable = {}       # Name -- Definition.
        Solver.mainSolver = self # The main solver object corresponds to the
                                 # last solver instantiated.

    def populateDefsTable(self, defs):
        """ @ warning: defs should be a list of pairs (name, definition)
        """
        for k,v in defs:
            # WARNING, it runs over old values if two keys are the same as it's 
            # a dictionary.
            self.defTable[k] = v

    def solveMath(self, formula):
        assert isinstance(formula, str)
        _result = 0
        p, rest = parseLine(formula, SUM, resultSoFar=[])
        if rest:
            raise NotMath(formula)
        try:
            _result = self.solveSum(p[0])
        except NoName as e:
            raise Exception("Can't solve " + formula + " because: " + str(e))
        return _result


    def solveSum(self, ast):
        assert isinstance(ast, Symbol)
        assert ast.__name__ == 'SUM'
        _result = 0

        _vs = ast.what[::2]  # values
        _os = [o for o in ast.what[1::2]] # operators
        _vss = [self.solveProd(v) for v in _vs]
        _result = _vss[0]
        assert len(_os) == len(_vss[1:])
        for o,v in zip(_os,_vss[1:]):
            if o == '+':
                _result += v
            elif o == '-':
                _result -= v
            else:
                assert False
        return _result



    def solveProd(self, ast):
        assert isinstance(ast, Symbol)
        assert ast.__name__ == 'PROD'
        _result = 0

        _vs = ast.what[::2]  # values
        _os = [ast2str(o) for o in ast.what[1::2]] # operators
        _vss = [self.solveVal(v) for v in _vs]
        _result = _vss[0]
        assert len(_os) == len(_vss[1:])
        for o,v in zip(_os,_vss[1:]):
            if o == '*':
                _result *= v
            elif o == '/':
                _result /= v
            elif o == '%':
                _result %= v
            else:
                assert False
        return _result


    def solveVal(self, ast):
        assert isinstance(ast, Symbol)
        assert ast.__name__ == 'VAL'
        _result = 0
        _sign = 1
        _aw = ast.what
        if _aw[0] == u'-':
            # it's a negative value
            _sign = -1
            _aw = _aw[1:]

        if _aw[0] == '(':
            # it's a SUM formula inside brackets
            _result = self.solveSum(_aw[1])
        elif isinstance(_aw[0], unicode) or isinstance(_aw[0], str): 
            # it's a number as its not '('
            _result = int(_aw[0])
        elif isinstance(_aw[0], Symbol):
            #it's a NAME
            _def = ""
            try:
                _def = self.defTable[str(ast2str(_aw[0]))]
            except:
                raise NoName(ast2str(_aw[0]))
            _result = self.solveMath(str(ast2str(_def)))
        else:
            raise TypeError(_aw[0])

        return _sign*_result

# MAIN =========================================================================

if __name__ == '__main__':

    svr = Solver()

    svr.defTable['A'] = '1'
    svr.defTable['B'] = '2'
    svr.defTable['C'] = '3'

    print ">>", svr.solveMath('(A+(B*C)--1)/4')
    print ">>", svr.solveMath('A+(B*C)')
    print ">>", svr.solveMath('(A+B)*C')
    print ">>", svr.solveMath('1')
    print ">>", svr.solveMath('(A+(D*C)--1)/4')

