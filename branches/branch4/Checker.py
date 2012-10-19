import Parser
import fileinput
import Debug
from Debug import debugCURRENT, debugERROR
from Types import Types
from Parser import _str, _cl
from Exceptions import *
import pyPEG
from GrammarRules import BOOLEXP, MATHEXP, COMMENT, SYMBCOMPARISON

############### MAIN
################################################################################
def Check(system):
    """
        Checks the correcteness of a System structure parsed by Parser.parse().
    """
    assert isinstance(system, Parser.System)

    checker = Checker()
    checker.check(system)






############### UTILITIES
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








############### CHECKER
################################################################################

class Checker():
    
    ########################################################################
    def __init__(self):
        self.sys = None
        self.typetable = {}
        self.setValuesTable = set([])
        self.allowevents = False
    
    ########################################################################
    def clear(self):
        self.__init__()        

    ########################################################################
    def check(self, sys):
        self.clear()
        self.sys = sys
        self.checkRedeclared()
        self.buildTypeTable()
        self.buildSetValuesTable()
        self.checkSystem()


    ########################################################################
    def checkRedeclared(self):
        #modules and instances are already checked during parsing
        
        for mod in self.sys.modules.itervalues():
            
            # REDECLARED VARIABLES:
            vset = set([])
            # context vars
            for cv in mod.contextvars:
                scv = _str(cv)
                if scv in vset:
                    raise LethalException( "Redeclared variable \'" + scv \
                                         + "\' in module \'" + mod.name \
                                         + "\', at line \'" + cv.__name__.line \
                                         + "\'.")
                vset.add(scv)
            # local vars
            for lv in mod.localvars:
                if lv.name in vset:
                    raise LethalException( "Redeclared variable \'" + lv.name \
                                         + "\' in module \'" + mod.name \
                                         + "\', at line \'" + lv.line + "\'.")
                vset.add(lv.name)

            # REDECLARED FAULTS
            fset = set([])
            for f in mod.faults:
                if f.name in fset:
                    raise LethalException( "Redeclared fault \'" + f.name \
                                         + "\' in module \'" + mod.name \
                                         + "\', at line \'" + f.line + "\'.")
                fset.add(f.name)

            # REDECLARED TRANSITIONS
            tset = set([])
            for t in mod.transitions:
                if t.name in tset:
                    raise LethalException( "Redeclared transition \'" + t.name \
                                         + "\' in module \'" + mod.name \
                                         + "\', at line \'" + t.line + "\'.")
                tset.add(t.name)



#........................ Type table building ..................................

    ########################################################################
    def buildTypeTable(self):

        # Local declared variables
        for inst in self.sys.instances.itervalues():
            self.typetable[inst.name] = {}
            mod = self.sys.modules[inst.module]
            for var in mod.localvars:
                self.typetable[inst.name][var.name] = var.type
                
        # context variables
        for inst in self.sys.instances.itervalues():
            mod = self.sys.modules[inst.module]
            n = len(mod.contextvars)
            for i in range(0,n):
                param = _str(inst.params[i])
                cvname = _str(mod.contextvars[i])
                try:
                
                    t = self.getType(param)
                    
                    if t != Types.Reference:
                        self.typetable[inst.name][cvname] = t
                    else:
                        # the ith contextvar in inst is a reference to another 
                        # instance
                        i = self.sys.instances[param]
                        m = self.sys.modules[i.module]
                        for v in m.localvars:
                            vname = cvname + "." + v.name
                            self.typetable[inst.name][vname] = v.type
                
                except UndeclaredError as e:
                
                    raise LethalException( "Undeclared variable <" + e.var \
                          + "> in <" + inst.name + "> instantiation" \
                          + ", at line <" + inst.params[i].__name__.line + ">." )
                
                
    ########################################################################
    def getType(self, vname):

        if isBool(vname):
            return Types.Bool
        elif isInt(vname):
            return Types.Int
        elif vname in self.sys.instances:
            return Types.Reference
        elif '.' in vname:
            i,v = vname.split('.',1)
            try:
                t = self.typetable[i][v]
                return t
            except KeyError as e:
                raise UndeclaredError(e.args[0], None)
        else:
            raise UndeclaredError(vname, None)

        assert False
        

#...............................................................................

    ########################################################################
    def buildSetValuesTable(self):
        for m in self.sys.modules.itervalues():
            for v in m.localvars:
                if v.type == Types.Symbol:
                    for x in v.domain:
                        self.setValuesTable.add(x)



    ########################################################################
    def checkSystem(self):
        self.checkVarSections()
        self.checkFaultSections()
        self.checkInitSections()


    ########################################################################
    def checkVarSections(self):
        for mod in self.sys.modules.itervalues():
            for var in mod.localvars:
                if var.type == Types.Int:
                    if int(var.domain[0]) > int(var.domain[1]):
                        raise LethalException( "Variable <" + var.name \
                              + "> in module <" + mod.name + "> at line <" \
                              + var.line + "> has an empty range.")
                if var.type == Types.Symbol:
                    for p in var.domain:
                        if isBool(p):
                            raise LethalException( "Cant use boolean value <" \
                                  + p + "> in set declaration" \
                                  + ", at line <" + var.line + ">.")


    ########################################################################
    
    def checkFaultSections(self):
        for inst in self.sys.instances.itervalues():
            mod = self.sys.modules[inst.module]
            for fault in mod.faults:
                # precondition
                try:
                    if _str(fault.pre) != "":
                        self.checkBoolExpresion(inst, _str(fault.pre))
                except NotBoolExpresionError as e:
                    raise LethalException("\'" + _str(fault.pre) \
                          + "\' should be a boolean expression. " \
                          + "In fault declaration at line <" + fault.line \
                          + ">." )
                
                # poscondition
                for elem in fault.pos:
                    leftside =  _str(elem[0])
                    rightside = _str(elem[1])
                    if self.moduleHasVar(mod.name, leftside):
                        tl = self.typetable[inst.name][leftside]
                        tr = Types.Notype
                        if elem[1].__name__ == "SIMPLEXPR":
                            try:
                                self.checkBoolExpresion(inst, rightside)
                                tr = Types.Bool
                            except BaseException:
                                pass
                            try:
                                self.checkMathExpresion(inst, rightside)
                                tr = Types.Int
                            except BaseException:
                                pass
                        elif elem[1].__name__ == "NEXTREF":
                            tr = self.getTypeFromTable(inst.name, rightside)
                        elif elem[1].__name__ == "SET":
                            self.checkSET(elem[1])
                            tr = Types.Symbol
                        elif elem[1].__name__ == "RANGE":
                            if int(_str(elem[1].what[0])) > \
                               int(_str(elem[1].what[2])):
                                raise LethalException("Empty range in next" \
                                      + " assignment \'" + _str(elem) \
                                      + "\', at line <" + fault.line + ">.")
                            tr = Types.Int
                        else:
                            assert False

                        assert tr != Types.Notype

                        # check correct types in assignment
                        if tl != tr and elem[1].__name__ != "SET":
                            tls = str(Types.Types[tl])
                            trs = str(Types.Types[tr])
                            line = str(elem[0].__name__.line)
                            raise LethalException(unicode(" Wrong types \'" \
                                  + tls \
                                  + "\' and \'" + trs + "\' in assignment \'" \
                                  + _str(elem[1]) + "\' to variable \'" \
                                  + _str(elem[0]) + "\', at line <" \
                                  + line + ">."))
                        
                    else:
                        raise LethalException( "Module <" + mod.name \
                                  + "> has no local variable named <" \
                                  + _str(elem[0]) \
                                  + ">. Error at line <" + fault.line + ">.")
                # affects
                if fault.type == Types.Byzantine:
                    for v in fault.affects:
                        if not self.moduleHasVar(mod.name, v):
                            raise LethalException( "Module <" + mod.name \
                                  + "> has no local variable named <" + v \
                                  + ">. Error at line <" + fault.line + ">.")

                elif fault.type == Types.Stop:
                    for t in fault.affects:
                        if not self.moduleHasTrans(mod.name, t):
                            raise LethalException( "Module <" + mod.name \
                                  + "> has no transition named <" + t \
                                  + ">. Error at line <" + fault.line + ">.")



    ########################################################################
    def moduleHasVar(self, mname, vname):
        return vname in [v.name for v in self.sys.modules[mname].localvars]


    ########################################################################
    def moduleHasTrans(self, mname, tname):
        return tname in [t.name for t in self.sys.modules[mname].transitions]



    ########################################################################
    def checkBoolExpresion(self, inst, expr):
        try:
            _ast, _rest = pyPEG.parseLine(expr,BOOLEXP,[],True,COMMENT,True)
            if _rest != "":
                raise NotBoolExpresionError(expr)

            self.typeCheck(inst, _ast)
            
        except SyntaxError as e:
            raise NotBoolExpresionError(expr)


    ########################################################################
    def checkMathExpresion(self, inst, expr):
        try:
            _ast, _rest = pyPEG.parseLine(expr,MATHEXP,[],True,COMMENT,True)
            if _rest != "":
                raise NotMathExpresionError(expr)

            self.typeCheck(inst, _ast)
            
        except SyntaxError as e:
            raise NotMathExpresionError(expr)
        




#............................ Type Checking ...................................#


    ########################################################################
    def typeCheck(self, inst, AST):
        assert len(AST) == 1
        AST = AST[0]
        assert isinstance(AST, pyPEG.Symbol)
        
        if AST.__name__ == "BOOLEXP":
            self.typeCheckBOOLEXP( inst, AST)
        elif AST.__name__ == "MATHEXP":
            self.typeCheckMATHEXP( inst, AST)
        else:
            assert False
        


    ########################################################################
    def typeCheckBOOLEXP(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "BOOLEXP"
        l = len(AST.what)
        self.typeCheckBOOLCOMP( inst, AST.what[0])
        if l > 1:
            self.typeCheckBOOLEXP( inst, AST.what[2])
            

    ########################################################################
    def typeCheckBOOLCOMP(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "BOOLCOMP"
        l = len(AST.what)
        self.typeCheckBOOLFORM( inst, AST.what[0])
        if l > 1:
            self.typeCheckBOOLCOMP( inst, AST.what[2])


    ########################################################################
    def typeCheckBOOLFORM(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "BOOLFORM"
        l = len(AST.what)
        self.typeCheckBOOLVAL( inst, AST.what[0])
        if l > 1:
            self.typeCheckBOOLFORM( inst, AST.what[2])


    ########################################################################
    def typeCheckBOOLVAL(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "BOOLVAL"
        l = len(AST.what)
        if l == 3:
            self.typeCheckBOOLEXP( inst, AST.what[1])
        elif l == 2:
            self.typeCheckBOOLVAL( inst, AST.what[1])
        elif l == 1:
            AST = AST.what[0]


            if AST.__name__ == "IDENT" or AST.__name__ == "COMPLEXID":
                # this raises undeclared error if it doesn't find the variable
                t = self.getTypeFromTable( inst.name, _str(AST))
                if not Types.Bool == t:
                    istype = Types.Types[t]
                    isnttype = Types.Types[Types.Bool]
                    raise WrongTypeError(_str(AST), istype, isnttype)


            elif AST.__name__ == "EVENT":
                if not self.allowevents:
                    raise EventNotAllowedError()
                else:
                    iname, tname = _str(AST.what[1]).split('.',1)
                    if not self.instanceHasTrans(iname, tname):
                        raise UndeclaredError(_str(AST.what[1]), -1)

            elif AST.__name__ == "COMPARISON":
                # Check if is a symbolic comparison rather 
                # than a math comparison.
                try:
                    _ast, _rest = pyPEG.parseLine( _str(AST), SYMBCOMPARISON \
                                                 , [], True, COMMENT, True)
                    if _rest != "":
                        raise SyntaxError()   #to go and check for math comparison
                    else:
                        _ast = _ast[0]
                        t1 = self.getTypeFromTable(inst.name,_str(_ast.what[0]))
                        t2 = self.getTypeFromTable(inst.name,_str(_ast.what[2]))
                        if t1 != t2:
                            t1name = Types.Types[t1]
                            t2name = Types.Types[t2]
                            raise WrongComparisonError( _str(_ast.what[0]) \
                                                      , _str(_ast.what[2]) \
                                                      , t1name, t2name)
                except SyntaxError as e:
                    # then its a math comparison, we check it:
                    self.typeCheckMATHEXP(inst, AST.what[0])
                    self.typeCheckMATHEXP(inst, AST.what[2])


            elif AST.__name__ == "BOOL":
                # OK THEN
                pass

            elif AST.__name__ == "INCLUSION":
            
                t = self.getTypeFromTable(inst.name, _str(AST.what[0]))
                if AST.what[2].__name__ == "RANGE":

                    if t != Types.Int:
                        istype = Types.Types[t]
                        isnttype = Types.Types[Types.Int]
                        raise WrongTypeError(_str(AST.what[0]),istype,isnttype)
                    
                    domain = AST.what[1].what
                    Debug.debugMAGENTA( "Should be a number: " \
                                      + str(int(domain[1])))
                    if int(domain[0]) > int(domain[1]):
                        raise EmptyRangeError(domain[0], domain[1])
                        
                elif AST.what[2].__name__ == "SET":
                    self.checkSET(AST.what[2])
            else:
                debugERROR("Internal error, \'" + AST.__name__ + "\' is wrong.")
                assert False
        else:
            assert False


    #######################################################################
    def typeCheckMATHEXP(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "MATHEXP"
        l = len(AST.what)
        self.typeCheckPRODUCT(inst, AST.what[0])
        if l > 1:
            self.typeCheckMATHEXP(inst, AST.what[2])


    #######################################################################
    def typeCheckPRODUCT(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "PRODUCT"
        l = len(AST.what)
        self.typeCheckMATHVAL(inst, AST.what[0])
        if l > 1:
            self.typeCheckPRODUCT(inst, AST.what[2])


    #######################################################################
    def typeCheckMATHVAL(self, inst, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "MATHVAL"
        l = len(AST.what)
        if l == 3 or l == 3:
            self.typeCheckMATHEXP(inst, AST.what[1])
        elif l == 1:
            AST = AST.what[0]
            if AST.__name__ == "INT":
                #OK THEN
                pass
            elif AST.__name__ == "IDENT" or AST.__name__ == "COMPLEXID":
                t = self.getTypeFromTable(inst.name, _str(AST))
                if t != Types.Int:
                    istype = Types.Types[t]
                    isnttype = Types.Types[Types.Int] # Pongo "Int" de una?
                    raise WrongTypeError(_str(AST), istype, isnttype)
            else:
                debugERROR("Internal Error: \'" + _str(AST) + "\'.")
                assert False
        else:
            assert False


    #######################################################################
    def checkSET(self, AST):
        assert isinstance(AST, pyPEG.Symbol)
        assert AST.__name__ == "SET"
        for x in AST.what:
            if x != ',' and x != '{' and x != '}':
                assert isinstance(x, pyPEG.Symbol)
                if x.__name__ == "IDENT":
                    if not x.what[0] in self.setValuesTable:
                        raise UndeclaredError(x.what[0])


    #######################################################################
    def getTypeFromTable(self, iname, vname):
        try:
            t = self.typetable[iname][vname]
            return t
        except KeyError:
            raise UndeclaredError(vname, -1)




#.......................... End Type Checking .................................#

    ########################################################################

    def checkInitSections(self):
        pass






# TESTS ........................................................................
if __name__ == "__main__":

    _file = fileinput.input()

    _sys = Parser.parse(_file)
 
    #Debug.colorPrint("debugGREEN", str(_sys))
 
    Debug.colorPrint("debugGREEN", "\n\nChecking ...")
    
    Check(_sys)

    Debug.colorPrint("debugGREEN", "it's OK!")

