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
from Utils import _cl, _str
from Utils import *
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

# TODO Aclarar que instancia se esta checkeando al levantar una excepcion de 
# tipos.

################################################################################

class Checker(object):
    #.......................................................................
    def __init__(self):
        self.sys             = None
        self.typetable       = {}
        # symbvaluetable contains symbol values that have been declared 
        # inside sets
        self.symbvaluetable  = []
        self.allowevents     = False
        self.allownextrefs   = False
        # We use this global instance to set the environment for expresions 
        # outside proctypes declarations.
        self.globalinst      = Parser.Instance()
        self.globalinst.name = "Glob#inst"
        
    
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
        self.checkProperties()
        self.checkContraints()
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


            s = fset.intersection(tset)
            l = list(s)
            if l != []:
                raise LethalE( "Error in proctype <" + pt.name \
                             + ">. Fault and transition with same name: <" \
                             + l[0] + ">.")


    #.......................................................................
    def checkInstancesParams(self):
        if self.sys.instances == {}:
            WARNING("No instances declared in input file.\n")
    
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            m = len(pt.synchroacts)
            
            # check same number of parameters
            if n+m != len(inst.params):
                raise LethalE("Incorrect number of parameters for instance <" \
                             + inst.name + "> at <" + inst.line + ">.")

            # check synchronization
            lst = []
            for p in inst.params[n::]:
                ps = _str(p)
                if ps not in lst:
                    lst.append(ps)
                else:
                    raise LethalE("Error concerning to synchronization name <" \
                                 + ps + "> in instanciation of <" + inst.name \
                                 + "> at <" + inst.line + ">. Can't " \
                                 + "synchronice between two transitions of "\
                                 + "the same instance.")

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
                    or param in [x.name for x in self.sys.instances.itervalues()]:
                        success = True
                else:
                    # is it an instance variable?
                    iname, vname = param.split('.', 1)
                    if iname in [x.name for x in self.sys.instances.itervalues()]:
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

        self.typetable[self.globalinst.name] = {}

        # Local declared variables
        for inst in self.sys.instances.itervalues():
            self.typetable[inst.name] = {}
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                self.typetable[inst.name][var.name] = var.type
                # simbol values 
                if var.type == Types.Symbol:
                    for value in var.domain:
                        self.typetable[inst.name][value] = Types.Symbol
                        self.typetable[self.globalinst.name][value]=Types.Symbol
                
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
                    ptt = self.sys.proctypes[i.proctype]
                    for v in ptt.localvars:
                        vname = cvname + "." + v.name
                        self.typetable[inst.name][vname] = v.type
                elif '.' in param:
                    i, v = param.split('.',1)
                    assert v in self.typetable[i]
                    self.typetable[inst.name][cvname] = self.typetable[i][v]
                else:
                    assert False

        # for global instance:
        giname = self.globalinst.name
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for v in pt.localvars:
                vname = inst.name + '.' + v.name
                self.typetable[giname][vname]=self.typetable[inst.name][v.name]

    #.......................................................................
    def checkInstancedProctypes(self):
        """
            Check for consistency in proctypes, and its instanciations.
        """
        for inst in self.sys.instances.itervalues():
            self.checkVarSection(inst)
            self.checkFaultSection(inst)
            self.checkInitSection(inst)
            self.checkTransSection(inst)
            

    #.......................................................................
    def checkVarSection(self, inst):
        pt = self.sys.proctypes[inst.proctype]
        for v in pt.localvars:
            if v.type == Types.Int:
                if v.domain[0] > v.domain[1]:
                    raise LethalE( "Empty range in declaration of \'" \
                                 + v.name + " at <" + v.line + ">.")
    #.......................................................................
    def checkFaultSection(self, inst):
        pt = self.sys.proctypes[inst.proctype]
        for f in pt.faults:
            # pre
            if f.pre != None:
                assert isinstance(f.pre, pyPEG.Symbol)
                assert f.pre.__name__ == "EXPRESION"
                t = self.getExpresionType(inst, f.pre)
                if t != Types.Bool:
                    raise LethalE( "Error at <" + f.line \
                                 + ">. Fault enable condition \'" \
                                 + putBrackets(f.pre) \
                                 + "\' should be Boolean type, but is " \
                                 + Types.Types[t] + " type instead.")
            # pos
            self.allownextrefs = True
            for p in f.pos:
                nextref = p[0]
                nrname = _str(nextref)
                expr = p[2]
                exprname = _str(expr)
                
                # expr must be a local declared var
                if not nrname in [x.name for x in pt.localvars]:
                    raise LethalE("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + nrname \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")
                
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
            self.allownextrefs = False
            # type
            for a in f.affects:
                sa = _str(a)
                line = a.__name__.line
                if f.type == Types.Byzantine:
                    if not sa in [x.name for x in pt.localvars]:
                        raise LethalE( "Undeclared variable \'" + sa \
                                     + "\' as byzantine affected variable" \
                                     + " for fault \'" + f.name + "\' at <" \
                                     + line + ">.")
                elif f.type == Types.Stop:
                    if not sa in [x.name for x in pt.transitions]:
                        raise LethalE( "Undeclared transition \'" + sa \
                                     + "\' as Stop affected transition" \
                                     + " for fault \'" + f.name + "\' at <" \
                                     + line + ">.")
                else:
                    assert False
    #.......................................................................
    def checkInitSection(self, inst):
        pt = self.sys.proctypes[inst.proctype]
        if pt.init != None:
            t = self.getExpresionType(inst, pt.init)
            if t != Types.Bool:
                line = getBestLineNumberForExpresion(pt.init)
                raise LethalE( "Init formula at <" + line \
                             + "> should be of Boolean type, but it's type " \
                             + Types.Types[t] +" instead.")

    #.......................................................................
    def checkTransSection(self, inst):
        pt = self.sys.proctypes[inst.proctype]
        # We have already checked that there is no repeated transition name.
        for tr in pt.transitions:
                        # pre
            if tr.pre != None:
                assert isinstance(tr.pre, pyPEG.Symbol)
                assert tr.pre.__name__ == "EXPRESION"
                t = self.getExpresionType(inst, tr.pre)
                if t != Types.Bool:
                    line = getBestLineNumberForExpresion(tr.pre)
                    raise LethalE( "Error at <" + line \
                                 + ">. Tranisition enable condition \'" \
                                 + putBrackets(tr.pre) \
                                 + "\' should be Boolean type, but is " \
                                 + Types.Types[t] + " type instead.")
            # pos
            self.allownextrefs = True
            for p in tr.pos:
                nextref = p[0]
                nrname = _str(nextref)
                expr = p[2]
                exprname = _str(expr)
                
                # expr must be a local declared var
                if not nrname in [x.name for x in pt.localvars]:
                    raise LethalE("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + nrname \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")
                
                
                t1 = self.getTypeFromTable(inst, nrname)
                if p[1] == "=":
                    t2 = self.getExpresionType(inst, expr)
                elif p[1] == "in":
                    t2 = self.getSetOrRangeType(inst, expr)
                else:
                    assert False

                if (p[1] == '=' and t1 != t2) \
                    or (p[1] == 'in' and t1 not in t2):
                    line = nextref.__name__.line
                    raise LethalE( "Wrong types <" + Types.Types[t1] \
                                 + "> (from \'" + nrname + "\') and <" \
                                 + Types.Types[t2] + "> (from \'" \
                                 + putBrackets(expr) \
                                 + "\'), in next equation of variable \'" \
                                 + nrname + "\' at <" + line + ">.")
            self.allownextrefs = False
    #.......................................................................
    def getSetOrRangeType(self, inst, expr):
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ in ["RANGE", "SET"]
        if expr.__name__ == "RANGE":
            if int(_str(expr.what[0])) > int(_str(expr.what[2])):
                raise LethalE( "Empty range \'" + _str(expr) 
                             + "\' at <" + str(line) + ">.")
            return [Types.Int]
        else:
            ts = set([])
            for elem in expr.what:
                if isinstance(elem, pyPEG.Symbol) and elem.__name__ == "IDENT":
                    ts.add(self.getTypeFromTable(inst.name, _str(elem)))
                elif isBool(_str(elem)):
                    ts.add(Types.Bool)
                elif isInt(_str(elem)):
                    ts.add(Types.Int)
                else:
                    pass
            return list(ts)
    #.......................................................................
    def checkProperties(self):
        for p in self.sys.properties.itervalues():
            t = p.type
            if t == Types.Ctlspec or t == Types.Ltlspec:
                self.checkTimeLogicExp(p.formula)
            elif t in [Types.Nb, Types.Fmfs, Types.Fmf]:
                self.checkTimeLogicExp(p.formula)
                for x in p.params:
                    # for Types.Fmf type properties
                    line = getBestLineNumberForExpresion(x)
                    if '.' not in _str(x):
                        raise LethalE("Bad fault name \'" + _str(x) \
                                     + "\' for Finitely many fault" \
                                     + " propertie at <" + line + ">.")
                    else:
                        i, f = _str(x).split('.',1)
                        try:
                            inst = self.sys.instances[i]
                            pt = self.sys.proctypes[inst.proctype]
                            if not f in [x.name for x in pt.faults]:
                                raise LethalE( "Error at <" + line \
                                             + ">. No fault named \'" \
                                             + f + "\' in instance \'" \
                                             + i + "\'.")
                        except KeyError as e:
                            raise LethalE( " Error at <" + line + ">. \'" \
                                         + i \
                                         + "\' doesn't name an instance.") 

    #.......................................................................
    def checkTimeLogicExp(self, expr):
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ in ["CTLEXP", "LTLEXP"]
        self.allowevents = True
        try:
            for exp in getExpresions(expr):
                t = self.getExpresionType(self.globalinst, exp)
                if t != Types.Bool:
                    exps = putBrackets(exp)
                    line = getBestLineNumberForExpresion(exp)
                    raise LethalE("Error at <" + line + ">. Expresions inside" \
                                 +" time logic properties must be of type " \
                                 +"bool, while \'" + exps + "\' is type " \
                                 + Types.Types[t] + ".")
            self.allowevents = False
        except BaseException as e:
            self.allowevents = False
            raise e
        
    #.......................................................................
    def checkContraints(self):
        self.allowevents = True
        try:
            for c in self.sys.contraints.itervalues():
                for exp in c.params:
                    t = self.getExpresionType(self.globalinst, exp)
                    if t != Types.Bool:
                        exps = putBrackets(exp)
                        line = getBestLineNumberForExpresion(exp)
                        self.allowevents = False
                        raise LethalE("Error at <" + line \
                                     + ">. Expresions inside time" \
                                     +" logic properties must be of type " \
                                     +"bool, while \'" + exps + "\' is type " \
                                     + Types.Types[t] + ".")
        except BaseException as e:
            self.allowevents = False
            raise e
    
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
                try:
                    return self.getTypeFromTable(inst, _str(value))
                except UndeclaredError as e:
                    line = value.__name__.line
                    raise LethalE("Error at <" + line + ">. " + e.error)
            elif value.__name__ == "NEXTREF":
                if not self.allownextrefs:
                    #raise NextRefNotAllowedE(value)
                    raise LethalE( "Error with <" + _str(value) + "'> at <" \
                                 + value.__name__.line \
                                 + ">. Next references aren't allowed here.")
                else:
                    # value must be a local declared var
                    values = _str(value)
                    pt = self.sys.proctypes[inst.proctype]
                    if not values in [x.name for x in pt.localvars]:
                        raise LethalE("Error at <" + expr.__name__.line \
                            + ">. Only local declared variables are allowed to be" \
                            + " used in next expresions. \'" + values \
                            + "\' isn't a local declared variable in proctype \'" \
                            + pt.name + "\'.")
                    return self.getTypeFromTable(inst, _str(value))
                assert False
            elif value.__name__ == "EVENT":
                if not self.allowevents:
                    #raise EventNotAllowedE(value)
                    raise LethalE( "Error with <" + _str(value) \
                                 + "> at <" + value.__name__.line \
                                 + ">. Events aren't allowed here.")
                else:
                    return self.getEventType(inst,value)
                assert False # never come out here
            elif value.__name__ == "INCLUSION":
                return self.getInclusionType(inst,value)
            else:
                assert False # never come out here
        else:
            assert False # never come out here
        assert False # never come out here

    #.......................................................................
    def getEventType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "EVENT"
        ev = ast.what[1]
        sv = _str(ev)
        if not '.' in sv:
            raise LethalE( "Bad value for event \'" + _str(ast) \
                         + "\' at <" + ast.__name__.line + ">.")
        else:
            ei,ev = sv.split('.', 1)
            try:
                einst = self.sys.instances[ei]
                ept = self.sys.proctypes[einst.proctype]
                elist=[x.name for x in ept.faults + ept.transitions]
                if not ev in elist:
                    line = getBestLineNumberForExpresion(ast)
                    raise LethalE("Error in event \'" + _str(ast) + "\', at <" \
                                 + line + ">. No event named \'" \
                                 + ev + "\' in instance \'" + ei + "\'.")
            except KeyError as e:
                line = getBestLineNumberForExpresion(ast)
                raise LethalE( "Error in event \'" + _str(ast) + "\', at <" \
                             + line + ">. \'" + ei \
                             + "\' doesn't name an instance.")
            return Types.Bool
            
        assert False # never come out here
    #.......................................................................
    def getInclusionType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "INCLUSION"
        elem = ast.what[0]
        t = self.getTypeFromTable(inst, _str(elem)) 
        _set = ast.what[2]
        if _set.__name__ == "SET":
            for x in _set.what:
                if isinstance(x,pyPEG.Symbol):
                    if x.__name__ == "IDENT":
                        #just to check if it exists.
                        try:
                            self.getTypeFromTable(inst, _str(x)) 
                        except UndeclaredError as e:
                            line = ast.__name__.line
                            raise LethalE( "Error at <" + line \
                                         + ">. " + e.error)
        elif _set.__name__ == "RANGE":
            line = _set.__name__.line
            if int(_str(_set.what[0])) > int(_str(_set.what[2])):
                raise LethalE( "Empty range \'" + _str(_set) 
                             + "\' at <" + str(line) + ">.")
            if t != Types.Int:
                ts = Types.Types[t]
                raise LethalE( "Can't check inclusion of an element " \
                             + "of type <" + ts \
                             + "> in a range, in \'" + _str(ast) \
                             + "\' at <" + line + ">.")
        else:
            assert False # never come out here
        return Types.Bool
    #.......................................................................

################################################################################

#TODO levantar excepcion por falta de instancias si es correcto hacerlo.

# TESTING ======================================================================


if __name__ == "__main__":

    _file = fileinput.input()

    _sys = Parser.parse(_file)
 
    #Debug.colorPrint("debugGREEN", str(_sys))
 
    Debug.colorPrint("debugGREEN", "\n\nChecking ...")
    
    Check(_sys)

    Debug.colorPrint("debugGREEN", "it's OK!")
#===============================================================================
