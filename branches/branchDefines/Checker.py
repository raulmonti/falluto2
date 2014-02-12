#===============================================================================
# Module Checker.py
# Author Raul Monti
# Mon 27 Jan 2014 05:57:07 PM ART 
#===============================================================================
#
from Parser import *
import Parser
from Debug import *
import Debug
from Exceptions import *
import Exceptions
from Types import *
from Utils import _cl, ss
from Utils import *
import Utils
import fileinput
#
#
#==============================================================================#
# PLAIN MODULE API ============================================================#
#==============================================================================#

def Check(model):
    """
        Checks the model for semantic correctness and raises exceptions if it's
        incorrect. Also print's warnings about diferent issues.

        @input model: a parsed Parser.Model instance with the model to check.
    """
    if not (isinstance(model, Parser.Model)):
        raise Critical("you are trying to check something that is not a model.")

    _checker = Checker()
    _checker.check(model)


#==============================================================================#
# CHECKER CLASS ===============================================================#
#==============================================================================#

class Checker(object):
    """ A checker looks up for semantic correctness in a parsed model. To do
        this you need to call de check method with a valid Parser.Model parsed
        model as its argument.
    """

    def __init__(self):
        self.mdl             = None
        self.typetable       = {}
        # symbvaluetable contains symbol values that have been declared 
        # inside sets.
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
    def check(self, model):
        assert isinstance(model, Parser.Model)
        self.clear()
        self.mdl = model
        self.checkRedeclared()
        self.checkInstancesParams()
        self.buildTypeTable()
        self.checkInstancedProctypes()
        self.checkProperties()
        self.checkContraints()
        self.checkDefines()

    #.......................................................................
    def checkRedeclared(self):
        """ Check the system for re-declared names. Redeclared modules and
            instances are already checked during parsing.
        """
        for _pt in self.mdl.proctypes.itervalues():
            # Redeclared variables:
            _vset = set([])
            # context vars
            for _cv in _pt.contextvars:
                _scv = ss(_cv)
                if _scv in _vset:
                    raise Error( "Redeclared variable \'" + _scv \
                               + "\' in proctype \'" + _pt.name \
                               + "\', at line \'" + _cv.__name__.line + "\'.")       
                _vset.add(_scv)
            # local vars
            for _lv in _pt.localvars:
                if _lv.name in _vset:
                    raise Error( "Redeclared variable \'" + _lv.name \
                               + "\' in proctype \'" + _pt.name \
                               + "\', at line \'" + _lv.line + "\'.")
                _vset.add(_lv.name)
                # set values (from symbol type variables)
                if _lv.type == Types.Symbol:
                    for _v in _lv.domain:
                        if _v in _vset:
                            raise Error( "Redeclared variable \'" + _v \
                                       + "\' in \'" + _lv.name + "\' domain" \
                                       + ", in proctype \'" + _pt.name \
                                       + "\', at line \'" + _lv.line + "\'.")
                        _vset.add(_v)
            # Redeclared faults
            _fset = set([])
            for _f in _pt.faults:
                if _f.name in _fset:
                    raise Error( "Redeclared fault \'" + _f.name \
                               + "\' in proctype \'" + _pt.name \
                               + "\', at line \'" + _f.line + "\'.")
                _fset.add(_f.name)
            # Check for empty intersection between faults and transitions
            _tset = set([_x.name for _x in _pt.transitions])
            _s = _fset.intersection(_tset)
            _l = list(_s)
            if _l != []:
                raise Error( "Error in proctype <" + _pt.name \
                           + ">. Fault and transition with same name: <" \
                           + _l[0] + ">.")

    #.......................................................................
    def checkInstancesParams(self):
        if self.mdl.instances == {}:
            WARNING("No instances declared in input file.\n")
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            n = len(pt.contextvars)
            m = len(pt.synchroacts)
            # check same number of parameters
            if n+m != len(inst.params):
                raise Error("Incorrect number of parameters for instance <" \
                           + inst.name + "> at <" + inst.line + ">.")
            # Context variables
            # TODO vale la pena agregar valores de tipo Symbol en el dominio de
            # las variables Symbol del proctype como posible context variable?
            # Es mas, es correcto pasar valores y no solo variables aqui?
            for i in range(0,n):
                param = ss(inst.params[i])
                success = False
                if not '.' in param:
                    # is it a boolean, an integer, or an instance name?
                    if isBool(param) \
                    or isInt(param)  \
                    or param in [x.name for x in self.mdl.instances.itervalues()]:
                        success = True
                else:
                    # is it an instance variable?
                    iname, vname = param.split('.', 1)
                    if iname in [x.name for x in self.mdl.instances.itervalues()]:
                        i = self.mdl.instances[iname]
                        pt = self.mdl.proctypes[i.proctype]
                        if vname in [x.name for x in pt.localvars]:
                            success = True
                if not success:
                    raise Error( "Undefined or bad parameter \'" \
                               + param + "\' in instance \'" + inst.name \
                               + "\' declaration at <" + inst.line + ">.")
            # Synchro actions
            # Can't have '.' in the names, to avoid collision with instance
            # actions.
            # TODO unificar estos 3 errores en uno solo que diga algo como:
            # 'Bad name 'param' for synchronous action'
            for i in range(n, len(inst.params)):
                param = ss(inst.params[i])
                if '.' in param:
                    raise Error( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use '.' in synchronous action " \
                                 + "names.")
                if isBool(param):
                    raise Error( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use a boolean value as a " \
                                 + "synchronous action name.")
                if isInt(param):
                    raise Error( "Error in instance \'" + inst.name \
                                 + "\' declaration at <" + inst.line \
                                 + ">. Can't use an integer value as a " \
                                 + "synchronous action name.")

    #.......................................................................
    def buildTypeTable(self):
        # Precondition: Instance parameters are well defined. 
        #               (use checkInstanceParameters method before this one)

        self.typetable[self.globalinst.name] = {}

        # Local declared variables
        for inst in self.mdl.instances.itervalues():
            self.typetable[inst.name] = {}
            pt = self.mdl.proctypes[inst.proctype]
            for var in pt.localvars:
                self.typetable[inst.name][var.name] = var.type
                # simbol values 
                if var.type == Types.Symbol:
                    for value in var.domain:
                        self.typetable[inst.name][value] = Types.Symbol
                        self.typetable[self.globalinst.name][value]=Types.Symbol

        # context variables
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for i in range(0,n):
                param = ast2str(inst.params[i])
                cvname = ast2str(pt.contextvars[i])

                if isBool(param):
                    self.typetable[inst.name][cvname] = Types.Bool
                    # and also for global reference at defines for example 
                    # (FIXME) this may not be needed or even incorrect.
                    self.typetable[self.globalinst.name][inst.name+'.'+cvname]\
                        = Types.Bool
                elif isInt(param):
                    self.typetable[inst.name][cvname] = Types.Int
                    self.typetable[self.globalinst.name][inst.name+'.'+cvname]\
                        = Types.Int
                elif param in self.mdl.instances:
                    # The ith contextvar in inst is a reference to another 
                    # instance.
                    i = self.mdl.instances[param]
                    ptt = self.mdl.proctypes[i.proctype]
                    for v in ptt.localvars:
                        vname = cvname + "." + v.name
                        self.typetable[inst.name][vname] = v.type
                        self.typetable[self.globalinst.name]\
                            [inst.name+'.'+cvname] = v.type
                elif '.' in param:
                    i, v = param.split('.',1)
                    assert v in self.typetable[i]
                    self.typetable[inst.name][cvname] = self.typetable[i][v]
                    self.typetable[self.globalinst.name][inst.name+'.'+cvname]\
                        = self.typetable[i][v]
                    #FIXME horrible duplicated code
                else:
                    assert False

        # for global instance:
        giname = self.globalinst.name
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            for v in pt.localvars:
                vname = inst.name + '.' + v.name
                self.typetable[giname][vname]=self.typetable[inst.name][v.name]

        # define variables, check them and add them to the type table
        self.checkDefines()

    #.......................................................................
    def checkDefines(self):
        """Look for redeclared define names. Also get the types for table."""
        # TODO los nombres de defines pueden chocar con los de tipos enumerados
        # solucionar para que eso no ocurra.
        defines = []
        for d in self.mdl.defs.itervalues():
            dname = Utils.ss(d.dname)
            if dname in defines:
                line = d.line
                raise Error( "Redeclared define name \'" + dname \
                           + "\' at <" + line + ">.")
            else:
                defines.append(dname)
        # check for circular dependence in definitions
        # TODO se hace tambien en tiempo de precompilacion, decidir donde esta
        # sobrando.
        adj = {}
        ss = set([])
        for d in self.mdl.defs.itervalues():
            dname = Utils.ss(d.dname)
            adj[dname] = [x for x in _cl(d.dvalue) if x in defines]
            ss = ss.union(set(adj[dname]))
        ss = ss.intersection(set(defines))
        cy = self.hasCycleDfs(adj, list(ss))
        if cy != []:
            raise Error( "Circular dependence in DEFINES declaration: " \
                       + commaSeparatedString(cy) + ".")
        #self.fillDefinesTypes(adj)

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
        for d in self.mdl.defs.itervalues():
            _dname = Utils.ss(d.dname)
            self.visited[_dname] = False
        for d,v in self.visited.iteritems():
            if not v:
                self.fillTypesDfs(adj,d)


    #....................................
    def fillTypesDfs(self, adj, r):

        for a in adj[r]:
            if not self.visited[a]:
                self.fillTypesDfs(adj,a)

        for d in self.mdl.defs.itervalues():
            dname = ss(d.dname)
            if  dname == r:
                # TODO darle tipo a los defines
                t = self.getExpresionType(self.globalinst, d.dvalue)
                # TODO dname puede estar pisando un nombre de tipo enumerado
                self.typetable[self.globalinst.name][dname] = t

                for inst in self.mdl.instances.itervalues():
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
        for inst in self.mdl.instances.itervalues():
            self.checkVarSection(inst)
            self.checkFaultSection(inst)
            self.checkInitSection(inst)
            self.checkTransSection(inst)
            

    #.......................................................................
    def checkVarSection(self, inst):
        # Solo reviso rango vacio para enteros
        pt = self.mdl.proctypes[inst.proctype]
        for v in pt.localvars:
            if v.type == Types.Int:
                if v.domain[0] > v.domain[1]:
                    raise Error( "Empty range in declaration of \'" \
                                 + v.name + " at <" + v.line + ">.")


    #.......................................................................
    def checkFaultSection(self, inst):
        pt = self.mdl.proctypes[inst.proctype]
        for f in pt.faults:
            # pre
            if f.pre != None:
                assert isinstance(f.pre, pyPEG.Symbol)
                assert f.pre.__name__ == "EXPRESION"
                t = self.getExpresionType(inst, f.pre)
                if t != Types.Bool:
                    raise Error( "Error at <" + f.line \
                                 + ">. Fault enable condition \'" \
                                 + putBrackets(f.pre) \
                                 + "\' should be Boolean type, but is " \
                                 + Types.Types[t] + " type instead.")
            # pos
            self.allownextrefs = True
            for p in f.pos:
                nextref = p[0]
                nrname = ss(nextref).split(" ")[0]
                expr = p[2]
                exprname = ss(expr)
                
                # expr must be a local declared var
                if not nrname in [x.name for x in pt.localvars]:
                    raise Error("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + ss(nextref) \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")
                
                t1 = self.getTypeFromTable(inst, nrname)
                if p[1] == '=':
                    t2 = self.getExpresionType(inst, expr)
                elif p[1] == 'in':
                    t2 = self.getSetOrRangeType(inst, expr)
                        
                
                if (p[1] == '=' and t1 != t2) \
                    or (p[1] == 'in' and not t1 in t2):
                    line = nextref.__name__.line
                    raise Error( "Wrong types <" + Types.Types[t1] \
                                 + "> (from \'" + nrname + "\') and <" \
                                 + Types.Types[t2] + "> (from \'" \
                                 + putBrackets(expr) \
                                 + "\'), in next equation of variable \'" \
                                 + nrname + "\' at <" + line + ">.")
            self.allownextrefs = False
            # type
            for a in f.affects:
                sa = ss(a)
                line = a.__name__.line
                if f.type == Types.Byzantine:
                    if not sa in [x.name for x in pt.localvars]:
                        raise Error( "Undeclared variable \'" + sa \
                                     + "\' as byzantine affected variable" \
                                     + " for fault \'" + f.name + "\' at <" \
                                     + line + ">.")
                elif f.type == Types.Stop:
                    if not sa in [x.name for x in pt.transitions]:
                        raise Error( "Undeclared transition \'" + sa \
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
            return ss(ast).split(" ")[0]


    #.......................................................................
    def checkInitSection(self, inst):
        pt = self.mdl.proctypes[inst.proctype]
        if pt.init != None:
            t = self.getExpresionType(inst, pt.init)
            if t != Types.Bool:
                line = getBestLineNumberForExpresion(pt.init)
                raise Error( "Init formula at <" + line \
                             + "> should be of Boolean type, but it's type " \
                             + Types.Types[t] +" instead.")

    #.......................................................................
    def checkTransSection(self, inst):
        pt = self.mdl.proctypes[inst.proctype]
        # We have already checked that there is no repeated transition name.
        for tr in pt.transitions:
                        # pre
            if tr.pre != None:
                assert isinstance(tr.pre, pyPEG.Symbol)
                assert tr.pre.__name__ == "EXPRESION"
                t = self.getExpresionType(inst, tr.pre)
                if t != Types.Bool:
                    line = getBestLineNumberForExpresion(tr.pre)
                    raise Error( "Error at <" + line \
                                 + ">. Tranisition enable condition \'" \
                                 + putBrackets(tr.pre) \
                                 + "\' should be Boolean type, but is " \
                                 + Types.Types[t] + " type instead.")
            # pos
            self.allownextrefs = True
            for p in tr.pos:
                nextref = p[0]
                nrname = ast2str(nextref)[:-1:]
                expr = p[1]
                exprname = ast2str(expr)
                
                # expr must be a local declared var
                if not nrname in [x.name for x in pt.localvars]:
                    raise Error("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + nrname \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")

                t1 = self.getTypeFromTable(inst, nrname)
                if p[1].__name__ == "EXPRESION":
                    t2 = self.getExpresionType(inst, expr)
                elif p[1].__name__ == "SET" or p[1].__name__ == "RANGE":
                    t2 = self.getSetOrRangeType(inst, expr)
                else:
                    assert False

                if (p[1] == '=' and t1 != t2) \
                    or (p[1] == 'in' and t1 not in t2):
                    line = nextref.__name__.line
                    raise Error( "Wrong types <" + Types.Types[t1] \
                               + "> (from \'" + nrname + "\') and <" \
                               + Types.Types[t2] + "> (from \'" \
                               + putBrackets(expr) \
                               + "\'), in next equation of variable \'" \
                               + nrname + "\' at <" + line + ">.")
            self.allownextrefs = False


    #.......................................................................
    def getSetOrRangeType(self, inst, expr):
        """
            Returns list of types for expr (sets can have diferent types 
            inside).
        """
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ in ["RANGE", "SET"]
        if expr.__name__ == "RANGE":
            if int(ss(expr.what[0])) > int(ss(expr.what[2])):
                raise Error( "Empty range \'" + ss(expr) 
                           + "\' at <" + str(line) + ">.")
            return [Types.Int]
        else:
            # expr.__name__ == "SET"
            ts = set([])
            for elem in expr.what[1:-1]:
                if isinstance(elem, pyPEG.Symbol) and elem.__name__ == "IDENT":
                    ts.add(self.tryToGetType(inst, elem, expr))
                elif isBool(ss(elem)):
                    ts.add(Types.Bool)
                elif isInt(ss(elem)):
                    ts.add(Types.Int)
                else:
                    if ss(elem) not in ['{',',','}']:
                        debugERROR(elem)
                        assert False
            return list(ts)

    #.......................................................................
    def checkProperties(self):
        for p in self.mdl.properties.itervalues():
            t = p.type
            if t == Types.Ctlspec or t == Types.Ltlspec:
                self.checkTimeLogicExp(p.formula)
            elif t in [Types.Nb, Types.Fmfs, Types.Fmf]:
                self.checkTimeLogicExp(p.formula)
                for x in p.params:
                    # for Types.Fmf type properties
                    line = getBestLineNumberForExpresion(x)
                    if '.' not in ss(x):
                        raise Error("Bad fault name \'" + ss(x) \
                                   + "\' for Finitely many fault" \
                                   + " propertie at <" + line + ">.")
                    else:
                        i, f = ss(x).split('.',1)
                        try:
                            inst = self.mdl.instances[i]
                            pt = self.mdl.proctypes[inst.proctype]
                            if not f in [x.name for x in pt.faults]:
                                raise Error( "Error at <" + line \
                                           + ">. No fault named \'" \
                                           + f + "\' in instance \'" \
                                           + i + "\'.")
                        except KeyError as e:
                            raise Error( " Error at <" + line + ">. \'" \
                                       + i \
                                       + "\' doesn't name an instance.") 

    #.......................................................................
    def checkTimeLogicExp(self, tlexpr):
        """ Checks for type correctenes inside properties especifications. """
        assert isinstance(tlexpr, pyPEG.Symbol)
        assert tlexpr.__name__ in ["CTLEXP", "LTLEXP"]
        self.allowevents = True
        try:
            for exp in getAst(tlexpr,["EXPRESION"]):
                t = self.getExpresionType(self.globalinst, exp)
                if t != Types.Bool:
                    exps = putBrackets(exp)
                    line = getBestLineNumberForExpresion(exp)
                    raise Error( "Error at <" + line + ">. Expresions inside" \
                               + " time logic properties must be of type " \
                               + "bool, while \'" + exps + "\' is type " \
                               + Types.Types[t] + ".")
            self.allowevents = False
        except BaseException as e:
            self.allowevents = False
            raise e

    #.......................................................................
    def checkContraints(self):
        self.allowevents = True
        try:
            for c in self.mdl.contraints.itervalues():
                for exp in c.params:
                    t = self.getExpresionType(self.globalinst, exp)
                    if t != Types.Bool:
                        exps = putBrackets(exp)
                        line = getBestLineNumberForExpresion(exp)
                        self.allowevents = False
                        raise Error("Error at <" + line \
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
        return self.getPROPType(inst, expr.what[0])

    #.......................................................................
    def getPROPType(self, inst, ast):

        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "PROP"
        
        l = len(ast.what)
        t1 = self.getLOGICType(inst, ast.what[0])
        if l == 1:
            return t1    
        elif l == 3:
            t2 = self.getPROPType(inst, ast.what[2])
            if t1 != Types.Bool or t2 != Types.Bool:
                line = ast.__name__.line
                raise WrongTFO(t1,t2,ast.what[1],ast,line)
            else:
                return Types.Bool
        else:
            assert False
        assert False # never come out here

    #.......................................................................
    def getLOGICType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "LOGIC"
        
        l = len(ast.what)
        t1 = self.getCOMPType(inst, ast.what[0])
        if l == 1:
            return t1    
        elif l == 3:
            t2 = self.getLOGICType(inst, ast.what[2])
            if t1 != Types.Bool or t2 != Types.Bool:
                line = ast.__name__.line
                raise WrongTFO(t1,t2,ast.what[1],ast,line)
            else:
                return Types.Bool
        else:
            assert False
        assert False # never come out here

    #.......................................................................
    def getCOMPType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "COMP"

        l = len(ast.what)
        t1 = self.getSUMType(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getCOMPType(inst, ast.what[2])
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
    def getSUMType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "SUM"

        l = len(ast.what)
        t1 = self.getPRODType(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getSUMType(inst, ast.what[2])
            op = ast.what[1]
            line = ast.__name__.line
            if t1 != Types.Int or t2 != Types.Int:
               raise WrongTFO(t1,t2,op,ast,line)
            return Types.Int
        else:
            assert False
        assert False # never come out here

    #.......................................................................
    def getPRODType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "PROD"

        l = len(ast.what)
        t1 = self.getValueType(inst, ast.what[0])
        if l == 1:
            return t1
        elif l == 3:
            t2 = self.getPRODType(inst, ast.what[2])
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
                raise Error( "Wrong type <" + ts + "> for operand \'" + op \
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
                    raise Error( "Error with <" + ss(value) + "'> at <" \
                                 + value.__name__.line \
                                 + ">. Next references aren't allowed here.")
                else:
                    # value must be a local declared var
                    values = ss(value).split(" ")[0]
                    pt = self.mdl.proctypes[inst.proctype]
                    if not values in [x.name for x in pt.localvars]:
                        raise Error("Error at <" + value.__name__.line \
                            + ">. Only local declared variables are allowed to be" \
                            + " used in next expresions. \'" + values \
                            + "\' isn't a local declared variable in proctype \'" \
                            + pt.name + "\'.")
                    return self.getTypeFromTable(inst, ss(value))
                assert False
            elif value.__name__ == "EVENT":
                if not self.allowevents:
                    #raise EventNotAllowedE(value)
                    raise Error( "Error with <" + ss(value) \
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
        arr, dum1, idx, dum2 = ss(subs).split(" ")
        try:
            array = self.getVarDeclaration(inst, arr)
        except:
            raise Error("Undeclared variable \'"+arr+"\' at <"+line+">.")
        if not array.isarray:
            raise Error( "Error at line <"+line+"> Can't subscribe to \'"\
                         + ss(subs).split(" ")[0] \
                         + "\' because it is not an array.")
        ub = int(array.range[1])
        lb = int(array.range[0])
        l = 0
        u = 0
        if array == None:
            raise Error("Undeclared variable \'"+arr+"\' at <"+line+">.")
        try:
            index = int(idx)
            l = int(idx)
            u = l
        except:
            try:
                index = self.getVarDeclaration(inst, idx)
                t = self.getTypeFromTable(inst, idx)
                if t != Types.Int:
                    raise Error("Invalid type \'"+Types.Types[t]\
                                 +"\' for subscription index. At <"+line\
                                 +">, inside \'"+ss(subs)+"\'.")
                u = int(index.domain[1])
                l = int(index.domain[0])
            except:
                raise Error("Undeclared variable \'"+idx+"\' at <"+line+">.")

        if u > ub or l < lb:
            raise Error("Subscription out of range at <"+line+">, inside \'"\
                         +ss(subs)+"\'.")
        
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
                    inst = self.mdl.instances[iname]
                    return self.getVarDeclaration(inst,vname)
                except:
                    raise UndeclaredError(varname)


        
        pt = self.mdl.proctypes[inst.proctype]
        
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
            if ss(x) == ctxname:
                break
            i += 1
        
        # can't find the varname in this instance        
        if i == len(pt.contextvars):
            raise UndeclaredError(varname)

        instanced = ss(inst.params[i], False)
        # instanced is an instance name
        if vname != "":
            newinst = self.mdl.instances[instanced]
            return self.getVarDeclaration(newinst, vname)

        # instanced is an variable name
        assert "." in instanced
        newiname, newvname = instanced.split(".",1)
        newinst = self.mdl.instances[newiname]
        return self.getVarDeclaration(newinst, newvname)


    #.......................................................................
    def getSynchroNamesList(self):
        _set = set([])
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for e in inst.params[n::]:
                _set.add(ss(e))
        return list(_set)


    #.......................................................................
    def getEventType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "EVENT"
        ev = ast.what[1]
        sv = ss(ev)
        if not '.' in sv:

            lst = self.getSynchroNamesList()
            if sv in lst:
                return Types.Bool
               
            line = getBestLineNumberForExpresion(ast)
            raise Error( "Error at <" + line + ">. There can't be no event" \
                         + " called \'" + ss(ast) + "\'.")               
        else:
            ei,ev = sv.split('.', 1)
            try:
                einst = self.mdl.instances[ei]
                ept = self.mdl.proctypes[einst.proctype]
                salst = [ss(x) for x in ept.synchroacts]
                elist = [ x.name for x in ept.faults + ept.transitions \
                          if x.name not in salst]
                if not ev in elist:
                    line = getBestLineNumberForExpresion(ast)
                    raise Error("Error in event \'" + ss(ast) + "\', at <" \
                                 + line + ">. No event named \'" \
                                 + ev + "\' in instance \'" + ei + "\'.")
            except KeyError as e:
                line = getBestLineNumberForExpresion(ast)
                raise Error( "Error in event \'" + ss(ast) + "\', at <" \
                             + line + ">. \'" + ei \
                             + "\' doesn't name an instance.")
            return Types.Bool
            
        assert False # never come out here

    #.......................................................................
    def tryToGetType(self, inst, elem, context):
        name = ss(elem).split(" ")[0] #split in case its a SUBSCRIPT
#        debugGREEN(name)
        ctxt = ss(context)
        line = getBestLineNumberForExpresion(elem)
        try:
            t = self.getTypeFromTable(inst, unicode(name))
            return t
        except UndeclaredError:
            raise Error( "Undeclared variable \'" + name + "\' at <" \
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
            if int(ss(_set.what[0])) > int(ss(_set.what[2])):
                raise Error( "Empty range \'" + ss(_set) 
                             + "\' at <" + str(line) + ">.")
            if t != Types.Int:
                ts = Types.Types[t]
                raise Error( "Can't check inclusion of an element " \
                             + "of type <" + ts \
                             + "> in a range, in \'" + ss(ast) \
                             + "\' at <" + line + ">.")
        else:
            assert False # never come out here
        return Types.Bool
    #.......................................................................

################################################################################


# TESTING ======================================================================


if __name__ == "__main__":

    try:
        print "__Arrancamos__"
        _file = sys.argv[1]
        _file = os.path.join(os.getcwd(), _file)
        debug('debugLBLUE', "Working on file: " + _file)
        _mdl = Parser.parse(_file)
        Debug.debug("debugGREEN", "Checking ...")
        Check(_mdl)
        Debug.debug("debugGREEN", "it's OK!")
    except Error, _e:
        debug("debugRED", str(_e))

    print "__Terminamos__"


#===============================================================================

# TODO levantar excepcion por falta de instancias si es correcto hacerlo.

# TODO Aclarar que instancia se esta checkeando al levantar una excepcion de 
# tipos. Quizas deberia distinguirse entre errores de tipado 'sintactico' y 
# aquellos que surgen de un erroneo pasaje de variables de contexto.

# TODO eliminar codigo basura (el que esta comentado y no sirve)

# TODO think that redeclared is not a word in any language. Change it if so
