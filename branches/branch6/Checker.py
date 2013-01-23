#===============================================================================
# Module Checker.py
# Author Raul Monti
#
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
# tipos. Quizas deberia distinguirse entre errores de tipado 'sintactico' y 
# aquellos que surgen de un erroneo pasaje de variables de contexto.

#TODO eliminar codigo basura (el que esta comentado y no sirve)

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
        # for dfs algorithms
        self.visited = {}
        self.stack = []


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
    #    self.checkDefines()
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
            tset = set([x.name for x in pt.transitions])
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

        # define variables, check them and add them to the type table
        self.checkDefines()

    #.......................................................................
    def checkDefines(self):

        # look for redeclared define names
        # TODO los nombres de defines pueden chocar con los de tipos enumerados
        # solucionar para que eso no ocurra.
        defines = []
        for d in self.sys.defines.itervalues():
            dname = _str(d.dname)
            if dname in defines:
                line = d.line
                raise LethalE( "Redeclared define name \'" + dname \
                             + "\' at <" + line + ">.")
            else:
                defines.append(dname)

        # check for circular dependence in definitions
        adj = {}
        ss = set([])
        for d in self.sys.defines.itervalues():
            dname = _str(d.dname)
            adj[dname] = [x for x in _cl(d.dvalue) if x in defines]
            ss = ss.union(set(adj[dname]))

        ss = ss.intersection(set(defines))
        cy = self.hasCycleDfs(adj, list(ss))
        if cy != []:
            raise LethalE( "Circular dependence in DEFINES declaration: " \
                         + symbolSeparatedTupleString(cy, symb = ',') + ".")

        self.fillDefinesTypes(adj)


    #....................................
    def hasCycleDfs(self, adj, leafs):
        self.stack = []
        self.visited = {}
        for d in adj:
            self.visited[d] = False
        """
        for d in leafs:
            if not self.visited[d]:
                try:
                    dfs(adj,d)
                except Exception:
                    return self.stack
        """            
        for e,v in self.visited.iteritems():
            if not v:
                try:
                    self.cycleDfs(adj,e)
                except Exception:
                    return self.stack
        # its acyclic:
        return []

    #....................................
    def cycleDfs(self, adj, r):
        for a in adj[r]:
            if a in self.stack:
                raise Exception(self.stack)
            else:
                self.stack.append(a)
            self.cycleDfs(adj, a)
        self.stack = self.stack[:-1:]


    #.......................................................................
    def fillDefinesTypes(self, adj):
        self.visited = {}
        for d in self.sys.defines.itervalues():
            dname = _str(d.dname)
            self.visited[dname] = False
        for d,v in self.visited.iteritems():
            if not v:
                self.fillTypesDfs(adj,d)


    #....................................
    def fillTypesDfs(self, adj, r):

        for a in adj[r]:
            if not self.visited[a]:
                self.fillTypesDfs(adj,a)

        for d in self.sys.defines.itervalues():
            dname = _str(d.dname)
            if  dname == r:
                t = self.getExpresionType(self.globalinst, d.dvalue)
                # TODO dname puede estar pisando un nombre de tipo enumerado
                self.typetable[self.globalinst.name][dname] = t

                for inst in self.sys.instances.itervalues():
                    try:
                        # local vars have precedence over defines
                        tt = self.typetable[inst.name][dname]
                    except:
                        self.typetable[inst.name][dname] = t
                self.visited[r] = True
                break

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
        # Solo reviso rango vacio para enteros
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
                nrname = _str(nextref).split(" ")[0]
                expr = p[2]
                exprname = _str(expr)
                
                # expr must be a local declared var
                if not nrname in [x.name for x in pt.localvars]:
                    raise LethalE("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + _str(nextref) \
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
    # TODO al dope esto, si es que no agrego mas utilidad
    def getName(self, ast):
        assert isinstance(ast, pyPEG.Symbol)
        if ast.__name__ == "NEXTREF":
            return _str(ast).split(" ")[0]


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
                nrname = _str(nextref).split(" ")[0]
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
            # expr.__name__ == "SET"
            ts = set([])
            for elem in expr.what:
                if isinstance(elem, pyPEG.Symbol) and elem.__name__ == "IDENT":
                    ts.add(self.tryToGetType(inst, elem, expr))
                elif isBool(_str(elem)):
                    ts.add(Types.Bool)
                elif isInt(_str(elem)):
                    ts.add(Types.Int)
                else:
                    if _str(elem) not in ['{',',','}']:
                        debugERROR(elem)
                        assert False
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
                return self.tryToGetType(inst, value, ast)
            elif value.__name__ == "NEXTREF":
                if not self.allownextrefs:
                    #raise NextRefNotAllowedE(value)
                    raise LethalE( "Error with <" + _str(value) + "'> at <" \
                                 + value.__name__.line \
                                 + ">. Next references aren't allowed here.")
                else:
                    # value must be a local declared var
                    values = _str(value).split(" ")[0]
                    pt = self.sys.proctypes[inst.proctype]
                    if not values in [x.name for x in pt.localvars]:
                        raise LethalE("Error at <" + value.__name__.line \
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
            elif value.__name__ == "SUBSCRIPT":
                return self.getSubscriptType(inst, value)
            else:
                assert False # never come out here
        else:
            assert False # never come out here
        assert False # never come out here

    #.......................................................................
    def getSubscriptType(self, inst, subs):
        assert isinstance(subs, pyPEG.Symbol)
        assert subs.__name__ == "SUBSCRIPT"
        line = getBestLineNumberForExpresion(subs)
        #subs.what = IDENT, re.compile(r" "), [IDENT,INT], re.compile(r"]")
        arr, dum1, idx, dum2 = _str(subs).split(" ")
        try:
            array = self.getVarDeclaration(inst, arr)
        except:
            raise LethalE("Undeclared variable \'"+arr+"\' at <"+line+">.")
        if not array.isarray:
            raise LethalE( "Error at line <"+line+"> Can't subscribe to \'"\
                         + _str(subs).split(" ")[0] \
                         + "\' because it is not an array.")
        ub = int(array.range[1])
        lb = int(array.range[0])
        l = 0
        u = 0
        if array == None:
            raise LethalE("Undeclared variable \'"+arr+"\' at <"+line+">.")
        try:
            index = int(idx)
            l = int(idx)
            u = l
        except:
            try:
                index = self.getVarDeclaration(inst, idx)
                t = self.getTypeFromTable(inst, idx)
                if t != Types.Int:
                    raise LethalE("Invalid type \'"+Types.Types[t]\
                                 +"\' for subscription index. At <"+line\
                                 +">, inside \'"+_str(subs)+"\'.")
                u = int(index.domain[1])
                l = int(index.domain[0])
            except:
                raise LethalE("Undeclared variable \'"+idx+"\' at <"+line+">.")

        if u > ub or l < lb:
            raise LethalE("Subscription out of range at <"+line+">, inside \'"\
                         +_str(subs)+"\'.")
        
        return self.tryToGetType(inst, subs, subs)

    #.......................................................................
    def getVarDeclaration(self, inst, varname):
        debugRED(inst)
        debugGREEN(varname)
        if inst.name == "Glob#inst":
            if not '.' in varname:
                raise UndeclaredError(varname)
            else:
                iname, vname = varname.split(".")
                try:
                    inst = self.sys.instances[iname]
                    return self.getVarDeclaration(inst,vname)
                except:
                    raise UndeclaredError(varname)


        
        pt = self.sys.proctypes[inst.proctype]
        
        #is it a local declared variable?:
        lst = [x for x in pt.localvars if x.name == varname]
        if lst != []:
            assert len(lst) == 1
            return lst[0] 

        # is it a context variable?:        
        ctxname = varname
        vname = ""
        if '.' in varname:
            ctxname, vname = varname.split(".",1)

        i = 0
        for x in pt.contextvars:
            if _str(x) == ctxname:
                break
            i += 1
        
        # can't find the varname in this instance        
        if i == len(pt.contextvars):
            raise UndeclaredError(varname)

        instanced = _str(inst.params[i], False)
        # instanced is an instance name
        if vname != "":
            newinst = self.sys.instances[instanced]
            return self.getVarDeclaration(newinst, vname)

        # instanced is an variable name
        assert "." in instanced
        newiname, newvname = instanced.split(".",1)
        newinst = self.sys.instances[newiname]
        return self.getVarDeclaration(newinst, newvname)


    #.......................................................................
    def getSynchroNamesList(self):
        _set = set([])
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for e in inst.params[n::]:
                _set.add(_str(e))
        return list(_set)


    #.......................................................................
    def getEventType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "EVENT"
        ev = ast.what[1]
        sv = _str(ev)
        if not '.' in sv:

            lst = self.getSynchroNamesList()
            if sv in lst:
                return Types.Bool
               
            line = getBestLineNumberForExpresion(ast)
            raise LethalE( "Error at <" + line + ">. There can't be no event" \
                         + " called \'" + _str(ast) + "\'.")               
        else:
            ei,ev = sv.split('.', 1)
            try:
                einst = self.sys.instances[ei]
                ept = self.sys.proctypes[einst.proctype]
                salst = [_str(x) for x in ept.synchroacts]
                elist = [ x.name for x in ept.faults + ept.transitions \
                          if x.name not in salst]
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
    def tryToGetType(self, inst, elem, context):
        name = _str(elem).split(" ")[0] #split in case its a SUBSCRIPT
        debugGREEN(name)
        ctxt = _str(context)
        line = getBestLineNumberForExpresion(elem)
        try:
            t = self.getTypeFromTable(inst, unicode(name))
            return t
        except UndeclaredError:
            raise LethalE( "Undeclared variable \'" + name + "\' at <" \
                         + line + ">, inside expresion \'" + ctxt + "\'.")

    #.......................................................................
    def getInclusionType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "INCLUSION"
        elem = ast.what[0]
        t = self.tryToGetType(inst, elem, ast)

        _set = ast.what[2]
        if _set.__name__ == "SET":
            for x in _set.what:
                if isinstance(x,pyPEG.Symbol):
                    if x.__name__ == "IDENT":
                        self.tryToGetType(inst, x, ast)

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
