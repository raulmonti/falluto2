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


debugTODO( "Mejorar el manejo de Excepciones :S colocar mas campos con valores"\
         + " y menos mensajes de error :D")



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
"""
    Get a list of the unicode objects in ast. Ast should have been build from
    pyPEG parsing methods.
"""
def _cl(ast = []):
    ret = []
    if isinstance(ast, Symbol):
        ret += _cl(ast.what)
    elif isinstance(ast, unicode):
        ret.append(unicode(ast))
    elif isinstance(ast, list):
        for x in ast:
            ret += _cl(x)
    else:
        raise TypeError(ast)
    return ret




################################################################################        
"""
    Get the string formed by the concatenation of the unicode objects in ast, 
    separated from each other by a space character. Ast should have been build 
    from pyPEG parsing methods.
"""
def _str(ast = []):
    lst = _cl(ast)
    string = ""
    if lst != []:
        string = lst[0]
    for element in lst[1::]:
        string += " " + element
    return string





################################################################################        
class SysTypeCheck(Types):

    def __init__(self, sys):
        Types.__init__(self)
        self.typetable = {}
        self.sys = sys
        self.BuildTypeTable()
        try:
            self.BuildTypeTable()
        except Exception as e:
            debugERROR(e)




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
                if var.type == self.Symbol:
                    for elem in var.domain:
                        self.VarTableAdd(inst.name, elem, var.type)
                
        for inst in self.sys.instances.itervalues():
            #context vars
            mod = self.sys.modules[inst.module]
            n = len(mod.contextVars)
            for j in range(0,n):
                v = inst.params[j]
                i, v = v.what.split('.',1)
                
                if i == inst.name:
                    raise CiclicDeclarationError(inst)

                try:
                    res = self.typetable[i][v]
                    self.typetable[inst.name][mod.contextVars[j]] = res
                except (NameError, KeyError) as e:
                    raise UndeclaredError(inst.params[j])



    ########################################################################
    def VarTableAdd(self, iname, AST, t):
        # TODO al vicio por ahora este chequeo porque agrego todos los instances 
        # names al comienzo.
        if iname in self.typetable:
            if AST.what in self.typetable[iname]:
                raise RedeclaredError(AST.what, [AST.__name__.line]) 
            else:
                self.typetable[iname][AST.what] = t
            



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
    
                #res = self.CheckTyping(inst.name, _str(init))
                try:
                    res = self.CheckTyping(inst.name, _str(init))
                except MyTypeError as e:
                    debugERROR( "Type error in <" + _str(e.exp) + " > at line "\
                              + init[0].__name__.line + ". It's " + e.istype \
                              + " but should be " + e.nottype)
                except Exception as e:
                    debugERROR(e)
                

    #######################################################################
    def CheckTyping (self, iname, expr):

        _ast = []
        rest = ""

        # Check if its an identifier
        try:
            _ast, rest = parseLine(expr, IDENT, [], True, None, True)
            if rest == "":
                return self.GetSymbolType(iname, _ast[0])
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



    ########################################################################
    def CheckExprType(self, iname, AST):
        AST = AST[0]
        if AST.__name__ == "BOOLPROP":
            self.CheckBOOLPROP(iname, AST)
            return Types.Bool
        elif AST.__name__ == "MATH":
            self.CheckMATH(iname, AST)
            return Types.Int
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
        l = len(AST)
        if l == 1:
            self.CheckMATHVAL(iname, AST[0])
        elif l == 3:
            self.CheckMATHVAL(iname, AST[0])
            self.CheckPROD(iname, AST[2])
        else:
            assert False
        


    def CheckMATHVAL(self, iname, AST):
        AST = AST.what
        l = len(AST)
        if l == 1:
            if isinstance(AST[0], Symbol):
                AST = AST[0]
                if AST.__name__ == "IDENT" or AST.__name__ == "COMPLEXID":

                    t = self.GetSymbolType(iname, AST)
                    if Types.Int != t:
                        raise MyTypeError( AST, self.types[t], \
                                           self.types[self.Int], iname)
                elif AST.__name__ == "INT":
                    pass
        elif l == 2 or l == 3:
            self.CheckMATH(iname, AST[1])
        else:
            assert False



    def CheckBOOLPROP(self, iname, AST):
        l = len(AST.what)
        if l == 1:
            self.CheckBOOLFORM(iname, AST.what[0])
        elif l == 3:
            self.CheckBOOLFORM(iname, AST.what[0])
            self.CheckBOOLPROP(iname, AST.what[2])
        else:
            assert False
    
    
    def CheckBOOLFORM(self, iname, AST):
        l = len(AST.what)
        if l == 1:
            self.CheckBOOLCOMP(iname, AST.what[0])
        elif l == 3:
            self.CheckBOOLCOMP(iname, AST.what[0])
            self.CheckBOOLFORM(iname, AST.what[2])
        else:
            assert False

    def CheckBOOLCOMP(self, iname, AST):
        l = len(AST.what)
        if l == 1:
            self.CheckBOOLVAL(iname, AST.what[0])
        elif l == 3:
            self.CheckBOOLVAL(iname, AST.what[0])
            self.CheckBOOLCOMP(iname, AST.what[2])
        else:
            assert False


    def CheckBOOLVAL(self, iname, AST):
        AST = AST.what
        l = len(AST)
        if l == 1:
            if isinstance(AST[0], Symbol):
                AST = AST[0]
                if AST.__name__ == "IDENT" or AST.__name__ == "COMPLEXID":
                    try:
                        t = self.GetSymbolType(iname, AST)
                        if Types.Bool != t:
                            raise MyTypeError( AST, self.types[t], \
                                               self.types[self.Bool], iname)
                    except Exception as e:
                        raise e
                elif AST.__name__ == "BOOL":
                    return
                else:
                    raise TypeError(AST)
        elif l == 2:
            self.CheckBOOLPROP(iname, AST[1])
        elif l == 3:
            if AST[0] == "(":
                self.CheckBOOLPROP(iname, AST[1])
            else:
                #Can be a comparison between symbols or between math expressions
                t1 = Types.Unknown
                t2 = Types.Unknown
                t1 = self.CheckTyping(iname, _str(AST[0]))
                t2 = self.CheckTyping(iname, _str(AST[2]))
                
                typelist = [self.types[self.Int], self.types[self.Symbol]]
                
                if t1 == Types.Bool:
                    raise MyTypeError( AST[0], self.types[t1], typelist, iname)
                if t2 == Types.Bool:
                    raise MyTypeError( AST[2], t2, [Types.Int, Types.Symbol]\
                                     , iname)
                if t1 != t2:
                    raise RongComparisonERROR( AST[0], self.types[t1], \
                                               self.types[t2], \
                                               "while parsing " + _str(AST))
                elif t1 == Types.Symbol:
                    if _str(AST[0]) != _str(AST[2]):
                        self.CheckSymbolInDomain(iname, AST[0],AST[2])                    
                               
        else:
            raise TypeError(AST)



    ########################################################################
    """
        Checks weather ast1 is a variable and ast2 belongs to its domain, or
        ast2 is a variable and ast1 belongs to its domain. Otherwise raises
        NotInDomainError. 
        @Note: If both are variables then it does nothing.
    """
    def CheckSymbolInDomain(self, iname, ast1, ast2):
        pass

