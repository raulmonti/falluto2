#===============================================================================
#===============================================================================
#
from Parser import *
import Parser
from Debug import *
import Debug
from Exceptions import *
import Exceptions
from Types import *
from Utils import _cl, _str, isBool, isInt, putBrackets
import Utils
import fileinput
#
#===============================================================================


# Plain module API =============================================================

#...............................................................................
#   Check():
#       system: Parser.System class object obtained from Parser.py parse 
#               function.
def Check(system):
    """
        Checks for system semantic correctness and raises exceptions if it's
        incorrect. Also print's warnings about diferent issues.
    """
    if not (isinstance(system, Parser.System)):
        raise LethalE("Error, trying to check something that is not a system.")

    _checker = Checker()
    _checker.check(system)
#...............................................................................

#===============================================================================


################################################################################

class Checker(object):
    #.......................................................................
    def __init__(self):
        self.sys           = None
        self.typetable     = {}
        self.allowevents   = False
        self.allownextrefs = False
    
    #.......................................................................
    def clear(self):
        self.__init__()        

    #.......................................................................
    def check(self, system):
        assert isinstance(system, Parser.System)
        self.clear()
        self.sys = system
        self.checkRedeclared()
        self.checkInstancesParams()
        self.buildTypeTable()
        self.checkInstancedProctypes()
    #.......................................................................
    def checkRedeclared(self):
        """
            Check the system for redeclared names.
        """
        #Redeclared modules and instances are already checked during parsing.
        
        for pt in self.sys.proctypes.itervalues():
            
            # REDECLARED VARIABLES:
            vset = set([])
            # context vars
            for cv in pt.contextvars:
                scv = _str(cv)
                if scv in vset:
                    raise LethalE( "Redeclared variable \'" + scv \
                                 + "\' in proctype \'" + pt.name \
                                 + "\', at line \'" + cv.__name__.line + "\'.")
                                
                vset.add(scv)
            # local vars
            for lv in pt.localvars:
                if lv.name in vset:
                    raise LethalE( "Redeclared variable \'" + lv.name \
                                 + "\' in proctype \'" + pt.name \
                                 + "\', at line \'" + lv.line + "\'.")
                vset.add(lv.name)
                # set values (from symbol type variables)
                if lv.type == Types.Symbol:
                    for v in lv.domain:
                        if v in vset:
                            raise LethalE( "Redeclared variable \'" + v \
                                         + "\' in \'" + lv.name + "\' domain" \
                                         + ", in proctype \'" + pt.name \
                                         + "\', at line \'" + lv.line + "\'.")
                        vset.add(v)

            # REDECLARED FAULTS
            fset = set([])
            for f in pt.faults:
                if f.name in fset:
                    raise LethalE( "Redeclared fault \'" + f.name \
                                 + "\' in proctype \'" + pt.name \
                                 + "\', at line \'" + f.line + "\'.")
                fset.add(f.name)

            # REDECLARED TRANSITIONS
            tset = set([])
            for t in pt.transitions:
                if t.name in tset:
                    raise LethalE( "Redeclared transition \'" + t.name \
                                 + "\' in proctype \'" + pt.name \
                                 + "\', at line \'" + t.line + "\'.")
                tset.add(t.name)

    #.......................................................................
    def checkInstancesParams(self):
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            
            # Context variables
            
            # TODO vale la pena agregar valores de tipo Symbol en el dominio de
            # las variables Symbol del proctype como posible context variable?
            # Es mas, es correcto pasar valores y no solo variables aqui?
            for i in range(0,n):
                param = _str(inst.params[i])
                success = False

                if not '.' in param:
                    # is it a boolean, an integer, or an instance name?
                    if isBool(param) \
                    or isInt(param)  \
                    or param in self.sys.instances:
                        success = True
                else:
                    # is it an instance variable?
                    iname, vname = param.split('.', 1)
                    if iname in self.sys.instances:
                        i = self.sys.instances[iname]
                        pt = self.sys.proctypes[i.proctype]
                        if vname in [x.name for x in pt.localvars]:
                            success = True
                
                if not success:
                    raise LethalE( "Undefined or bad parameter \'" \
                                 + param + "\' in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line + ">.")
            # Synchro actions
            # Can't have '.' in the names, to avoid collision with instance
            # actions.
            # TODO unificar estos 3 errores en uno solo que diga algo como:
            # 'Bad name 'param' for synchronous action'
            for i in range(n, len(inst.params)):
                param = _str(inst.params[i])
                if '.' in param:
                    raise LethalE( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use '.' in synchronous action " \
                                 + "names.")
                if isBool(param):
                    raise LethalE( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use a boolean value as a " \
                                 + "synchronous action name.")
                if isInt(param):
                    raise LethalE( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use an integer value as a " \
                                 + "synchronous action name.")

    #.......................................................................
    def buildTypeTable(self):
        # Precondition: Instance parameters are well defined. 
        #               (use checkInstanceParameters method before this one)

        # Local declared variables
        for inst in self.sys.instances.itervalues():
            self.typetable[inst.name] = {}
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                self.typetable[inst.name][var.name] = var.type
                if var.type == Types.Symbol:
                    for value in var.domain:
                        self.typetable[inst.name][value] = Types.Symbol
                
        # context variables
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for i in range(0,n):
                param = _str(inst.params[i])
                cvname = _str(pt.contextvars[i])
                
                if isBool(param):
                    self.typetable[inst.name][cvname] = Types.Bool
                elif isInt(param):
                    self.typetable[inst.name][cvname] = Types.Int
                elif param in self.sys.instances:
                    # The ith contextvar in inst is a reference to another 
                    # instance.
                    i = self.sys.instances[param]
                    pt = self.sys.proctypes[i.proctype]
                    for v in pt.localvars:
                        vname = cvname + "." + v.name
                        self.typetable[inst.name][vname] = v.type
                elif '.' in param:
                    i, v = param.split('.',1)
                    assert v in self.typetable[i]
                    self.typetable[inst.name][cvname] = self.typetable[i][v]
                else:
                    debugRED(param)
                    assert False

    #.......................................................................
    def checkInstancedProctypes(self):
        """
            Check for consistency in proctypes, and its instanciations.
        """
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            
            # VAR section
            for v in pt.localvars:
                if v.type == Types.Int:
                    if v.domain[0] > v.domain[1]:
                        raise LethalE( "Empty range in declaration of \'" \
                                     + v.name + " at <" + v.line + ">.")
            
            # FAULT section
            for f in pt.faults:
                # pre
                if f.pre != None:
                    assert isinstance(f.pre, pyPEG.Symbol)
                    assert f.pre.__name__ == "EXPRESION"
                    t = self.getExpresionType(inst, f.pre)
                    if t != Types.Bool:
                        raise LethalE( "Error at <" + f.line 
                                     + ">. Fault enable condition \'" 
                                     + putBrackets(f.pre) 
                                     + "\' should be Boolean type, but is " 
                                     + Types.Types[t] + " type instead.")
                # pos
                for p in f.pos:
                    nextref = p[0]
                    nrname = _str(nextref)
                    expr = p[2]
                    exprname = _str(expr)
                    
                    t1 = self.getTypeFromTable(inst, nrname)
                    t2 = self.getExpresionType(inst, expr)
                    
                    if (p[1] == '=' and t1 != t2) \
                        or (p[1] == 'in' and t2 == Types.Int and t1 != t2):
                        line = nextref.__name__.line
                        raise LethalE( "Wrong types <" + Types.Types[t1] \
                                     + "> (from \'" + nrname + "\') and <" \
                                     + Types.Types[t2] + "> (from \'" \
                                     + putBrackets(expr) \
                                     + "\'), in next equation of variable \'" \
                                     + nrname + "\' at <" + line + ">.") 
                # type
    #.......................................................................
    def getTypeFromTable(self, inst, vname):
        try:
            t = self.typetable[inst.name][vname]
            return t
        except KeyError:
            raise UndeclaredError(vname)
        
    #.......................................................................
    def getExpresionType(self, inst, expr):
        """
            Returns the type of expr (a pyPEG.Symbol object obtained using the
            'EXPRESION' rule in GrammarRules.py).
            In the process of doing it, it checks for Type inconsistence and
            undeclared names in the expresion.
        """
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ == "EXPRESION"
        return self.getLevel5Type(inst, expr.what[0])

    #.......................................................................
    def getLevel5Type(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LEVEL5"
        
        l = len(ast.what)
        t1 = self.getLevel4Type(inst, ast.what[0])
        if l == 1:
            return t1    
        elif l == 3:
            t2 = self.getLevel5Type(inst, ast.what[2])
            if t1 != Types.Bool or t2 != Types.Bool:
                line = ast.__name__.line
                raise WrongTFO(t1,t2,ast.what[1],ast,line)
            else:
                return Types.Bool
        else:
            assert False
        assert False # never come out here
    #.......................................................................
    def getLevel4Type(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LEVEL4"
        
        l = len(ast.what)
        t1 = self.getLevel3Type(inst, ast.what[0])
        if l == 1:
            return t1    
        elif l == 3:
            t2 = self.getLevel4Type(inst, ast.what[2])
            if t1 != Types.Bool or t2 != Types.Bool:
                line = ast.__name__.line
                raise WrongTFO(t1,t2,ast.what[1],ast,line)
            else:
                return Types.Bool
        else:
            assert False
        assert False # never come out here
    #.......................................................................
    def getLevel3Type(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LEVEL3"

        l = len(ast.what)
        t1 = self.getLevel2Type(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getLevel3Type(inst, ast.what[2])
            op = ast.what[1]
            line = ast.__name__.line
            if op in ['>=','<=','<','>']:
                if t1 != Types.Int or t2 != Types.Int:
                    raise WrongTFO(t1,t2,op,ast,line)
            elif op in ['=','!=']:
                if t1 != t2:
                    raise WrongTFO(t1,t2,op,ast,line)
            else:
                assert False
            return Types.Bool
        else:
            assert False
        assert False # never come out here
    #.......................................................................
    def getLevel2Type(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LEVEL2"

        l = len(ast.what)
        t1 = self.getLevel1Type(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getLevel2Type(inst, ast.what[2])
            op = ast.what[1]
            line = ast.__name__.line
            if t1 != Types.Int or t2 != Types.Int:
               raise WrongTFO(t1,t2,op,ast,line)
            return Types.Int
        else:
            assert False
        assert False # never come out here
    #.......................................................................
    def getLevel1Type(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LEVEL1"

        l = len(ast.what)
        t1 = self.getValueType(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getLevel1Type(inst, ast.what[2])
            op = ast.what[1]
            line = ast.__name__.line
            if t1 != Types.Int or t2 != Types.Int:
               raise WrongTFO(t1,t2,op,ast,line)
            return Types.Int
        else:
            assert False
        assert False # never come out here
    #.......................................................................
    def getValueType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "VALUE"

        l = len(ast.what)
        if l == 3:
            return self.getLevel5Type(inst, ast.what[1])
        elif l == 2:
            op = ast.what[0]
            assert op in ['!', '-']
            t = self.getValueType(inst, ast.what[1])
            if(op == '-' and t != Types.Int) or (op == '!' and t != Types.Bool):
                ts = Types.Types[t]
                line = ast.__name__.line
                exp = putBrackets(ast)
                raise LethalE( "Wrong type <" + ts + "> for operand \'" + op \
                             + "\' in \'" + exp + "\', at <" + line + ">.")
            else:
                return t
        elif l == 1:
            value = ast.what[0]
            if value.__name__ == "INT":
                return Types.Int
            elif value.__name__ == "BOOL":
                return Types.Bool
            elif value.__name__ == "IDENT":
                return self.getTypeFromTable(inst, _str(value))
            elif value.__name__ == "NEXTREF":
                if not self.allownextrefs:
                    raise NextRefNotAllowedE(value)
                else:
                    return self.getTypeFromTable(inst, _str(value))
                assert False
            elif value.__name__ == "EVENT":
                if not self.allowevents:
                    raise EventNotAllowedE(value)
                else:
                    return self.getTypeFromTable(inst, _str(value))
                assert False
            elif value.__name__ == "INCLUSION":
                elem = value.what[0]
                t = self.getTypeFromTable(inst, _str(elem)) 
                _set = value.what[2]
                if _set.__name__ == "SET":
                    for x in _set.what:
                        if isinstance(x,pyPEG.Symbol):
                            if x.__name__ == "IDENT":
                                #just to check if it exists.
                                self.getTypeFromTable(inst, _str(x)) 
                elif _set.__name__ == "RANGE":
                    line = _set.__name__.line
                    if int(_str(_set.what[0])) > int(_str(_set.what[2])):
                        raise LethalE( "Empty range \'" + _str(_set) 
                                     + "\' at <" + str(line) + ">.")
                    if t != Types.Int:
                        ts = Types.Types[t]
                        raise LethalE( "Can't check inclusion of an element " \
                                     + "of type <" + ts \
                                     + "> in a range, in \'" + _str(value) \
                                     + "\' at <" + line + ">.")
                else:
                    assert False
                return Types.Bool
            else:
                assert False
        else:
            assert False
        assert False
    #.......................................................................

################################################################################


# TESTING ======================================================================


if __name__ == "__main__":

    _file = fileinput.input()

    _sys = Parser.parse(_file)
 
    #Debug.colorPrint("debugGREEN", str(_sys))
 
    Debug.colorPrint("debugGREEN", "\n\nChecking ...")
    
    Check(_sys)

    Debug.colorPrint("debugGREEN", "it's OK!")
#===============================================================================
