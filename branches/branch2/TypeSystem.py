################################################################################
# Module Typing.py
# For Falluto 2.0 Model checker front end
#
# Raul Monti
# lun 24 Septiembre 2012
#
# Module in charge of the typing system
#
################################################################################


from Exceptions import UndeclaredError
from Debug import colorPrint
import fileinput
from Parser import *
from pyPEG import Symbol

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
        #Checking parameters
        self.acceptEvents = False
        self.inst = None    #instance to take account as context while checking in tables
        #
        self.actionTable = {}
        self.typetable = {}
        self.sys = sys
        try:
            self.BuildTypeTable()
        except Exception as e:
            debugERROR(e)
        try:
            self.BuildActionTable()
        except Exception as e:
            debugERROR(e)


    ########################################################################
    def BuildActionTable(self):
        pass


    ########################################################################
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
                    raise UndeclaredError( inst.params[j].what\
                                         , inst.line\
                                         , "Nothing")



    ########################################################################
    def VarTableAdd(self, iname, AST, t):
    
        assert iname in self.typetable
        
        if AST.what in self.typetable[iname]:
            raise RedeclaredError(AST.what, [AST.__name__.line]) 
        else:
            self.typetable[iname][AST.what] = t
            

    ########################################################################
    """
        Search the type of the symbol in its instance context. If it isn't a
        valid symbol then it will raise UndeclaredError.
    """
    def GetSymbolType(self, sname): #instance name and symbol name
        assert isinstance(sname, Symbol)
        name = sname.what
        if isInt(name):
            return Types.Int
        elif isBool(name):
            return Types.Bool
        else:
            try:
                res = self.typetable[self.inst.name][name]
                return res
            except:
                raise InvalidSymbolError(name, sname.__name__.line, \
                                         self.inst.name)



    ########################################################################
    """
        Check everything we can from the system :D.
    """
    def Check(self):
        self.CheckFaults()
        self.CheckInits()
        self.CheckTrans()
        self.CheckInstances()
                


    ########################################################################
    def CheckFaults(self):
    
        # Check for redeclared faults:
        for mod in self.sys.modules.itervalues():
            faultlist = []
            for fault in mod.faults:
                if fault.name in faultlist:
                    raise RedeclaredFault(fault.name, fault.line)
                else:
                    faultlist.append(fault.name)
        
        #
        for inst in self.sys.instances.itervalues():
            #configure checking parameters
            self.acceptEvents = False
            self.inst = inst
            #
            mod = self.sys.modules[inst.module]
            for fault in mod.faults:
                #check fault precondition to be of type bool
                if fault.pre != None:
                    self.CheckBOOLPROP(fault.pre)
                #check fault posconditions
                for nextval in fault.pos:
                    self.CheckNextVal(nextval)
                #check fault types
                for elem in fault.affects:
                    if elem.what not in \
                    [x.name for x in self.sys.modules[inst.module].trans]:
                        raise Exception( "Error at line " 
                                       + str(elem.__name__.line) + " in fault "\
                                       + "type declaration. No transition "\
                                       + "named << " + elem.what + " >>.")


    ########################################################################
    def CheckInits(self):
        
        for inst in self.sys.instances.itervalues():
            self.inst = inst
            self.acceptEvents = False;

            mod = self.sys.modules[inst.module]
            self.CheckBOOLPROP(mod.init[0])


    ########################################################################
    def CheckTrans(self):
        
        for inst in self.sys.instances.itervalues():
            self.inst = inst
            self.acceptEvents = False;

            mod = self.sys.modules[inst.module]
            for trans in mod.trans:
                if trans.pre != None:
                    self.CheckBOOLPROP(trans.pre)
                for nextval in trans.pos:
                    self.CheckNextVal(nextval)


    ########################################################################
    def CheckInstances(self):
        
        for inst in self.sys.instances.itervalues():
            mod = self.sys.modules[inst.module]
            n = len(mod.contextVars)
            assert n == len(inst.params[:n:])
            for elem in inst.params[:n:]:
                if elem.__name__ == "COMPLEXID":
                    iname, vname = elem.what.split('.',1)
                    try:
                        instance = self.sys.instances[iname]
                        vlist = [x.name for x in mod.localVars]
                        if vname not in vlist:
                            line = elem.__name__.line
                            raise InstHasNoVarError(iname, vname, line)
                    except Exception as e:
                        raise NoInstanceError(iname, elem.__name__.line)


    ########################################################################
    def CheckNextVal(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "NEXTVAL"
        nextvar = AST.what[0]
        value = AST.what[1]
        try:
            t = self.GetSymbolType(nextvar)
        except InvalidSymbolError as e:
            raise UndeclaredError(e.name, e.line, e.iname)
       
        if value.__name__ == "ONLYID":
            try:
                vt = self.GetSymbolType(value.what[0])
            except InvalidSymbolError as e:
                raise UndeclaredError(e.name, e.line, e.iname)
            if t != vt :
                raise InvalidNextAssignError( _str(nextvar), _str(value), \
                                          Types.types[t],\
                                          Types.types[vt], AST.__name__.line,\
                                          self.inst.name)
        elif value.__name__ == "BOOLPROP":
            self.CheckBOOLPROP(value)
            if t != Types.Bool:
                raise InvalidNextAssignError( _str(nextvar), _str(value), \
                                          Types.types[t], \
                                          Types.types[Types.Bool], \
                                          AST.__name__.line, \
                                          self.inst.name)
        elif value.__name__ == "MATH":
            self.CheckMATH(value)
            if t != Types.Int:
                raise InvalidNextAssignError( _str(nextvar), _str(value), \
                                          Types.types[t], \
                                          Types.types[Types.Int], \
                                          AST.__name__.line, \
                                          self.inst.name)
        elif value.__name__ == "NEXTREF":
            try:
                vt = self.GetSymbolType(value.what[0])
            except InvaludSymbolError as e:
                raise UndeclaredError(e.name, e.line, e.iname)
            if t != vt:
                raise InvalidNextAssignError( _str(nextvar), _str(value), \
                                          Types.types[t], \
                                          Types.types[vt], AST.__name__.line, \
                                          self.inst.name)                
        elif value.__name__ == "RANGE":
            self.CheckRANGE(symbol)
        elif value.__name__ == "SET":
            pass
        else:
            assert False
       

    ########################################################################
    def CheckBOOLPROP(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "BOOLPROP"
        l = len(AST.what)
        try:
            self.CheckBOOLCOMP(AST.what[0])
        except MyTypeError as e:
            raise WrongTypeBoolError(e.name,_str(AST),str(e.line),e.iname)
        if l > 1:
            self.CheckBOOLPROP(AST.what[2])



    ########################################################################
    def CheckBOOLCOMP(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "BOOLCOMP"
        l = len(AST.what)
        try:
            self.CheckBOOLFORM(AST.what[0])
        except MyTypeError as e:
            if l > 1:
                raise WrongTypeBoolError(e.name,_str(AST),str(e.line),e.iname)
            else:
                raise e
        if l > 1:
            self.CheckBOOLCOMP(AST.what[2])


    ########################################################################
    def CheckBOOLFORM(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "BOOLFORM"
        l = len(AST.what)
        try:
            self.CheckBOOLVAL(AST.what[0])
        except MyTypeError as e:
            if l > 1:
                raise WrongTypeBoolError(e.name,_str(AST),str(e.line),e.iname)
            else:
                raise e
        if l > 1:
            self.CheckBOOLFORM(AST.what[2])


    ########################################################################
    def CheckBOOLVAL(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "BOOLVAL"
        l = len(AST.what)
        if l == 2:
            self.CheckBOOLVAL(AST.what[1])
        elif l == 3:
            self.CheckBOOLPROP(AST.what[1])
        else:
            assert isinstance(AST.what[0], Symbol)
            symb = AST.what[0]
            if symb.__name__ == "EVENT":
                self.CheckEvent(symb)
            elif symb.__name__ == "INCLUSSION":
                self.CheckInclussion(symb)
            elif symb.__name__ == "BOOL":
                pass
            elif symb.__name__ == "COMPARISON":
                self.CheckCOMPARISON(symb)
            elif symb.__name__ == "COMPLEXID" or symb.__name__ == "IDENT":
                try:
                    t = self.GetSymbolType(symb)
                except InvalidSymbolError as e:
                    raise UndeclaredError(e.name, e.line, e.iname)
                if t != Types.Bool:
                    raise MyTypeError(symb.what, Types.types[t], 
                                      Types.types[Types.Bool], \
                                      symb.__name__.line, self.inst.name)
                


    ########################################################################
    def CheckCOMPARISON(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "COMPARISON"
        if AST.what[0].__name__ == "MATH":
            self.CheckMATH(AST.what[0])
            self.CheckMATH(AST.what[2])
        else:
            try:
                t1 = self.GetSymbolType(AST.what[0])
                t2 = self.GetSymbolType(AST.what[2].what[0])
            except InvalidSymbolError as e:
                raise UndeclaredError(e.name, e.line, e.iname)
            if t1 != t2:
                raise WrongComparisonError(_str(AST), Types.types[t1],\
                                            Types.types[t2], \
                                            AST.__name__.line, self.inst.name)




    ########################################################################
    def CheckEvent(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "EVENT"
        if not self.acceptEvents:
            raise CantUseEventsError( _str(AST), AST.__name__.line)
        else:
            cmpxId = AST.what[0].what[1]
            inst, act = cmpxId.split('.',1)
            if not act in self.ActionTable[inst]:
                raise InstHasNoActionError(inst,act,AST.what[0].__name__.line)


    ########################################################################
    def CheckInclussion(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "INCLUSSION"
        domain = AST.what[2]
        if domain.__name__ == "SET":
            self.CheckSET(domain)
        elif domain.__name__ == "RANGE":
            self.CheckRANGE(domain)
        else:
            assert False

    ########################################################################
    def CheckSET(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "SET"
        for elem in AST.what:
            if elem.__name__ == "IDENT":
                # TODO Check for someting??
                pass
                    

    ########################################################################
    def CheckRANGE(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "RANGE"
        if int(AST.what[0]) > int(AST.what[1]):
            raise WrongRangeError(_str(AST), AST.__name__.line)


    ########################################################################
    def CheckMATH(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "MATH"
        l = len(AST.what)
        self.CheckPRODUCT(AST.what[0])
        if l > 1:
            self.CheckMATH(AST.what[2])
        
    ########################################################################
    def CheckPRODUCT(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "PRODUCT"
        l = len(AST.what)
        self.CheckMATHVAL(AST.what[0])
        if l > 1:
            self.CheckPRODUCT(AST.what[2])

    ########################################################################
    def CheckMATHVAL(self, AST):
        assert isinstance(AST, Symbol)
        assert AST.__name__ == "MATHVAL"
        l = len(AST.what)
        if l > 1:
            self.CheckMATH(AST.what[1])
        else:
            symb = AST.what[0]
            assert isinstance(symb, Symbol)
            if symb.__name__ == "INT":
                pass
            elif symb.__name__ == "IDENT" or symb.__name__ == "COMPLEXID":
                try:
                    t = self.GetSymbolType(symb)
                except InvalidSymbolError as e:
                    raise UndeclaredError(e.name, e.line, e.iname)
                if t != Types.Int:
                    raise MyTypeError(_str(AST), Types.types[t], \
                                      Types.types[Types.Int], \
                                      AST.__name__.line, self.inst.name)
            else:
                assert False
            

#.............................TESTING...........................................


if __name__ == "__main__":
    
    _file = fileinput.input()
    parser = Parser()
    _sys = parser.parse(_file)
    colorPrint("debugGREEN", "Checking...")
    tcheck = SysTypeCheck(_sys)
    tcheck.Check()
    

