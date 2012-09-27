################################################################################
# Module Typing.py
# For Falluto 2.0 Model check front end
#
# Raul Monti
# lun 24 Septiembre 2012
#
# Module in charge of the typing system
#
################################################################################


from pyPEG import Symbol, parseLine
from Exceptions import *
from Debug import *
from SemanticRules import *


################################################################################        

class MyTypeError(Exception):
    def __init__(self, couse, where):
        Exception.__init__(self)
        self.couse = couse
        self.where = where
    def __repr__(self):
        return str(self.couse) + " In " + self.where


################################################################################        

class Types():
    Unknown = -1
    Bool = 0
    Int = 1
    Symbol = 2
    
    types = ["Bool","Int","Symbol"]

    def __init__(self):
        pass



################################################################################        
def isInt(var):
    try:
        int(var)
        return True
    except ValueError:
        return False


################################################################################        
def isBool(var):
    return var == "TRUE" or var == "FALSE"
    


################################################################################        
def _cl(ast = [], check = False, expect = None):
    ret = []
    if isinstance(ast, Symbol):
        ret += cleanAST(ast.what)
    elif isinstance(ast, unicode):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += cleanAST(x)
    return ret
    



################################################################################        
class SysTypeCheck(Types):

    def __init__(self, sys):
        Types.__init__(self)
        self.typetable = {}
        self.sys = sys
        self.BuildTypeTable()




################################################################################
    """
        Fill the type table with types of variables in each instance. 
        @ Note: Also checks for ciclic and for unexistent context variables 
                declarations.
    """
    def BuildTypeTable(self):
        # table first level (instances names)
        for inst in self.sys.instances.itervalues():
            self.typetable[inst.name] = {}

        for inst in self.sys.instances.itervalues():
            # local vars
            for var in self.sys.modules[inst.module].localVars:
                self.typetable[inst.name][var.name] = var.type
                
        for inst in self.sys.instances.itervalues():
            #contect vars
            mod = self.sys.modules[inst.module]
            n = len(mod.contextVars)
            for j in range(0,n):
                v = inst.params[j]
                i, v = v.what.split('.',1)
                
                if i == inst.name:
                    raise Exception("Cant use self variables to pass as "\
                                  + "context variable at instance " \
                                  + inst.name + " at line " + inst.line)

                try:
                    res = self.typetable[i][v]
                    self.typetable[inst.name][mod.contextVars[j]] = res
                except (NameError, KeyError) as e:
                    raise UndeclaredError(inst.params[j])


    ########################################################################
    """
        Search the type of the symbol in its instance context. If it isn't a
        valid symbol then it will raise UndeclaredError.
    """
    def GetSymbolType(self, iname, sname): #instance name and symbol name
        assert isinstance(sname, Symbol)
        name = sname.what
        if isInt(name):
            return Types.Int
        elif isBool(name):
            return Types.Bool
        else:
            try:
                res = self.typetable[iname][name]
                return res
            except:
                raise InvalidSymbolError(sname)



    ########################################################################
    def check(self):
        for inst in self.sys.instances.itervalues():
            for init in self.sys.modules[inst.module].init:
                print inst.name , init
                res = self.CheckTyping(inst.name,"hola+4")
                debugRED(res)
                debugRED(Types.types[res])

        


    """"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

    def CheckTyping (self, iname, expr):

        _ast = []
        rest = ""

        # Check if its an identifier
        try:
            _ast, rest = parseLine(expr, IDENT, [], True, None, True)
            if rest == "":
                ident = _cl(_ast)
                return self.GetSymbolType(iname, ident)
        except SyntaxError:
            pass    # didn't match with IDENT
        except InvalidSymbolError as e:
            raise e # The identifier doesn't exists
        
        
        # The same if its a complex identifier
        try:
            _ast = parseLine(expr, COMPLEXID, [], True, None, True)
            if rest == "":
                ident = _cl(_ast)
                return self.GetSymbolType(iname, ident)
        except SyntaxError:
            pass    # didn't match with IDENT
        except InvalidSymbolError as e:
            raise e # The identifier doesn't exists
        
        # Is it a BOOLPROP?
        try:
            _ast, rest = parseLine(expr, BOOLPROP, [], True, None, True)
            if rest == "":
                return self.CheckExprType(iname, _ast)
        except SyntaxError as e:
            pass # Didn't match simple propform

        # Is it a MATH expression?
        try:
            _ast, rest = parseLine(expr, MATH, [], True, None, True)
            if rest == "":
                return self.CheckExprType(iname, _ast)
        except SyntaxError as e:
            pass # Didn't match simple expresion        

        raise SyntaxError( "There is grammatical error in " + expr 
                         + " while instancing " + iname + ", but "\
                         + " can't realice what it is :S" )



    def CheckExprType(self, iname, AST):
        AST = AST[0]
        debugLBLUE(AST)
        if AST.__name__ == "BOOLPROP":
            try:
                self.CheckBOOLPROP(iname, AST)
                return Types.Bool
            except Exception as e:
                raise e
        elif AST.__name__ == "MATH":
            try:
                self.CheckMATH(iname, AST)
                return Types.Int
            except Exception as e:
                print e
                raise e
        else:
            assert False


    def CheckMATH(self, iname, AST):
        self.CheckSUM(iname, AST.what[0])


    def CheckSUM(self, iname, AST):
        l = len(AST.what)
        if l == 1:
            self.CheckPROD(iname, AST.what[0])
        elif l == 3:
            self.CheckPROD(iname, AST.what[0])
            self.CheckSUM(iname, AST.what[2])
        else:
            assert False
            
    def CheckPROD(self, iname, AST):
        AST = AST.what
        print AST
        l = len(AST)
        if l == 1:
            self.CheckMATHVAL(iname, AST[0])
        elif l == 3:
            self.CheckMATHVAL(iname, AST[0])
            self.CheckPROD(iname, AST[2])
        else:
            assert False
        
    def CheckMATHVAL(self, iname, AST):
        debugRED(AST)
        AST = AST.what
        debugGREEN(AST)
        l = len(AST)
        if isinstance(AST[0], Symbol):
            AST = AST[0]
            if AST.__name__ == "IDENT" or AST.__name__ == "COMPLEXID":
                try:
                    t = self.GetSymbolType(iname, AST)
                    if Types.Int != t:
                        raise MyTypeError( repr(AST), t, Types.Int, iname)
                except Exception as e:
                    debugRED(e.__class__.__name__)
                    raise e

        """if self.__name__ == IDENT:
            try:
                t = self.GetSymbolType(iname, AST.what[0])
                if Types.Int != t:
                    raise MyTypeError(_str(AST), types[t], "Int", iname)
            except Exception as e:
                raise e
        elif self.__name__ == 
        """



















