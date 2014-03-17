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
from Utils import ast2lst, ast2str
from Utils import *
import Utils
import fileinput
from Parser import VarDeclaration
VType = VarDeclaration.VarType
#
#
#==============================================================================#
# PLAIN MODULE API ============================================================#
#==============================================================================#

def check(model):
    """
        Checks the model for semantic correctness and raises exceptions if it's
        incorrect. Also print's warnings about diferent issues.

        @input model: a parsed Parser.Model instance with the model to check.
        @warning: make sure to make sintax replacements to your model before
                  using this. Use SyntaxRepl module for that.
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

    #-----------------------------------------------------------------------
    def clear(self):
        self.__init__()        

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
    def checkRedeclared(self):
        """ Check the system for re-declared names. Redeclared modules and
            instances are already checked during parsing.
        """
        for _pt in self.mdl.proctypes.itervalues():
            # Redeclared variables:
            _vset = set([])
            # context vars
            for _cv in _pt.contextvars:
                _scv = ast2str(_cv)
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

    #-----------------------------------------------------------------------
    def checkInstancesParams(self):
        if self.mdl.instances == {}:
            LWARNING("No instances declared in input file.")
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
                param = ast2str(inst.params[i])
                success = False
                if not '.' in param:
                    # is it a boolean, an integer, or an instance name?
                    if isBool(param) \
                    or isInt(param)  \
                    or param in\
                        [x.name for x in self.mdl.instances.itervalues()]:
                        success = True
                else:
                    # is it an instance variable?
                    iname, vname = param.split('.', 1)
                    if iname in\
                        [x.name for x in self.mdl.instances.itervalues()]:
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
                param = ast2str(inst.params[i])
                if '.' in param or isBool(param) or isInt(param):
                    raise Error("Bad name <" + param + "> for synchronous"\
                               +" action in instance <" + inst.name\
                               +"> at line <" + inst.line + ">.")

    #-----------------------------------------------------------------------

    def buildTypeTable(self):
        """ Build a dictionary whit entries [instance name][var name]
            and the parsed type structure of the correponding local variable 
            declarations as values.
            
            @Precondition: Instance parameters are well defined. 
                           (use checkInstanceParameters method before this one)
        """
        self.typetable[self.globalinst.name] = {}
        # Local declared variables
        for inst in self.mdl.instances.itervalues():
            self.typetable[inst.name] = {}
            pt = self.mdl.proctypes[inst.proctype]
            for var in pt.localvars:
                self.typetable[inst.name][var.name] = var.type
                # simbol values get a Types.Symbol VarType even dough they are
                # constants and not variables. FIXME?
                if var.type.type == Types.Symbol:
                    for value in var.type.domain:
                        self.typetable[inst.name][value] = VType(Types.Symbol)
                        self.typetable[self.globalinst.name][value]\
                            = VType(Types.Symbol)

        # context variables
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for i in range(0,n):
                param = ast2str(inst.params[i])
                cvname = ast2str(pt.contextvars[i])
                if isBool(param):
                    self.typetable[inst.name][cvname] = VType(Types.Bool)
                    # and also for global reference at properties for example.
                    self.typetable[self.globalinst.name][inst.name+'.'+cvname]\
                        = VType(Types.Bool)
                elif isInt(param):
                    self.typetable[inst.name][cvname] = VType(Types.Int)
                    self.typetable[self.globalinst.name][inst.name+'.'+cvname]\
                        = VType(Types.Int)
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
                    #FIXME duplicated code :S
                else:
                    assert False

        # for global instance:
        giname = self.globalinst.name
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            for v in pt.localvars:
                vname = inst.name + '.' + v.name
                self.typetable[giname][vname]=self.typetable[inst.name][v.name]

        # print the typetable
        #for i,v in self.typetable.iteritems():
        #    for x, y in v.iteritems():
        #        print i, x, y

    #-----------------------------------------------------------------------
    def checkInstancedProctypes(self):
        """
            Check for consistency in proctypes, and its instanciations.
        """
        for inst in self.mdl.instances.itervalues():
            self.checkVarSection(inst)
            self.checkFaultSection(inst)
            self.checkInitSection(inst)
            self.checkTransSection(inst)
            

    #-----------------------------------------------------------------------
    def checkVarSection(self, inst):
        # Solo reviso rango vacio para enteros
        pt = self.mdl.proctypes[inst.proctype]
        for v in pt.localvars:
            if v.type == Types.Int:
                if v.domain[0] > v.domain[1]:
                    raise Error( "Empty range in declaration of \'" \
                                 + v.name + " at <" + v.line + ">.")


    #-----------------------------------------------------------------------
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
                nrname = ast2str(nextref).split(" ")[0]
                expr = p[2]
                exprname = ast2str(expr)
                localname = nrname
                if nextref.__name__ == 'SUBSCRIPT':
                    t1 = self.getSubscriptType(inst,nextref)
                    localname = nrname.split('[')[0]
                else:
                    t1 = self.getTypeFromTable(inst, nrname)

                # expr must be a local declared var
                if not localname in [x.name for x in pt.localvars]:
                    raise Error("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + ast2str(nextref) \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")

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
                sa = ast2str(a)
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

    #-----------------------------------------------------------------------
    # TODO al dope esto, si es que no agrego mas utilidad
    def getName(self, ast):
        assert isinstance(ast, pyPEG.Symbol)
        if ast.__name__ == "NEXTREF":
            return ast2str(ast).split(" ")[0]


    #-----------------------------------------------------------------------
    def checkInitSection(self, inst):
        pt = self.mdl.proctypes[inst.proctype]
        if pt.init != None:
            t = self.getExpresionType(inst, pt.init)
            if t != Types.Bool:
                line = getBestLineNumberForExpresion(pt.init)
                raise Error( "Init formula at <" + line \
                             + "> should be of Boolean type, but it's type " \
                             + Types.Types[t] +" instead.")

    #-----------------------------------------------------------------------
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
                nextref = p[0].what[0]
                t1 = -1
                nrname = ast2str(nextref)
                localname = nrname         
                if nextref.__name__ == 'SUBSCRIPT':
                    t1 = self.getSubscriptType(inst,nextref)
                    localname = nrname.split('[')[0]
                else:
                    t1 = self.getTypeFromTable(inst, nrname)

                expr = p[1]
                exprname = ast2str(expr)
                
                # expr must be a local declared var
                if not localname in [x.name for x in pt.localvars]:
                    raise Error("Error at <" + expr.__name__.line \
                        + ">. Only local declared variables are allowed to be" \
                        + " used in next expresions. \'" + nrname \
                        + "\' isn't a local declared variable in proctype \'" \
                        + pt.name + "\'.")

                
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


    #-----------------------------------------------------------------------
    def getSetOrRangeType(self, inst, expr):
        """
            Returns list of types for expr (sets can have diferent types 
            inside).
        """
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ in ["RANGE", "SET"]
        if expr.__name__ == "RANGE":
            if int(ast2str(expr.what[0])) > int(ast2str(expr.what[2])):
                raise Error( "Empty range \'" + ast2str(expr) 
                           + "\' at <" + str(line) + ">.")
            return [Types.Int]
        else:
            # expr.__name__ == "SET"
            ts = set([])
            for elem in expr.what[1:-1]:
                if isinstance(elem, pyPEG.Symbol) and elem.__name__ == "IDENT":
                    ts.add(self.tryToGetType(inst, elem, expr))
                elif isBool(ast2str(elem)):
                    ts.add(Types.Bool)
                elif isInt(ast2str(elem)):
                    ts.add(Types.Int)
                else:
                    if ast2str(elem) not in ['{',',','}']:
                        assert False
            return list(ts)

    #-----------------------------------------------------------------------
    def checkProperties(self):
        for p in self.mdl.properties.itervalues():
            self.checkTimeLogicExp(p.formula)
            t = p.type
            #FIXME p.params should be p.faults (change it starting at parser.py)
            for x in p.params:
                # check faults named in properties parameters
                line = getBestLineNumberForExpresion(x)
                if '.' not in ast2str(x):
                    raise Error("Bad fault name \'" + ast2str(x) \
                               + "\' for Finitely many fault" \
                               + " propertie at <" + line + ">."
                               , ast2str(p.pypeg)
                               , "line " + str(line))
                else:
                    i, f = ast2str(x).split('.',1)
                    try:
                        inst = self.mdl.instances[i]
                        pt = self.mdl.proctypes[inst.proctype]
                        if not f in [x.name for x in pt.faults]:
                            raise Error("No fault named \'" + f\
                                       + "\' in instance \'" + i + "\'."
                                       , ast2str(p.pypeg)
                                       , "line " + str(line))
                    except KeyError as e:
                        raise Error( "'"+ i + "' doesn't name an instance."
                                   , ast2str(p.pypeg)
                                   , "line " + str(line) )
            # check actions named in properties parameters
            for a in p.actions:
                line = getBestLineNumberForExpresion(a)
                if '.' not in ast2str(a):
                    raise Error("No action named '"+ast2str(a)+"'."
                               , ast2str(p.pypeg)
                               , "line " + str(line))
                else:
                    i, a = ast2str(a).split('.',1)
                    try:
                        inst = self.mdl.instances[i]
                        pt = self.mdl.proctypes[inst.proctype]
                        if not a in [x.name for x in pt.transitions]:
                            #FIXME declare error texts somewhere else to be
                            # cleaner, us % to handel variables in the text.
                            raise Error( "No action named \'" + a +
                                         "\' in instance \'" + i + "\'."
                                       , ast2str(p.pypeg)
                                       , "line "+ str(line))
                    except KeyError as e:
                        raise Error( "'"+ i + "' doesn't name an instance."
                                   , ast2str(p.pypeg)
                                   , "line " + str(line) )
            # check limit for Atmost and Ensure properties
            if p.type in [Types.Ensure, Types.Atmost] and\
                int(ast2str(p.limit)) < 0:
                raise Error("Property limit should be greater than 0, and it's"\
                           +" <" + str(p.limit) +">.", ast2str(p.pypeg)
                           , getBestLineNumberForExpresion(p.formula))

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
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


    #-----------------------------------------------------------------------
    def getTypeFromTable(self, inst, vname):
        try:
            t = self.typetable[inst.name][vname].type
            return t
        except KeyError:
            raise UndeclaredError(vname)
        
    #-----------------------------------------------------------------------
    def getExpresionType(self, inst, expr):
        """
            Returns the type of expr (a pyPEG.Symbol object obtained using the
            'EXPRESION' rule in GrammarRules.py).
            In the process of doing it, it checks for Type inconsistence and
            undeclared names in the expresion.
        """
        assert isinstance(expr, pyPEG.Symbol)
        assert expr.__name__ == 'EXPRESION'
        return self.getPROPType(inst, expr.what[0])

    #-----------------------------------------------------------------------
    def getPROPType(self, inst, ast):

        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == 'PROP'
        
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

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
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

    #-----------------------------------------------------------------------
    def getValueType(self, inst, ast):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "VALUE"

        l = len(ast.what)
        if l == 3:
            return self.getPROPType(inst, ast.what[1])
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
                    raise Error( "Error with <" + ast2str(value) + "'> at <" \
                                 + value.__name__.line \
                                 + ">. Next references aren't allowed here.")
                else:
                    # value must be a local declared var
                    values = ast2str(value).split(" ")[0]
                    pt = self.mdl.proctypes[inst.proctype]
                    if not values in [x.name for x in pt.localvars]:
                        raise Error("Error at <" + value.__name__.line \
                            + ">. Only local declared variables are allowed "\
                            + "to be used in next expresions. \'" + values\
                            + "\' isn't a local declared variable in "\
                            + "proctype \'" + pt.name + "\'.")
                    return self.getTypeFromTable(inst, ast2str(value))
                assert False
            elif value.__name__ == "EVENT":
                if not self.allowevents:
                    #raise EventNotAllowedE(value)
                    raise Error( "Error with <" + ast2str(value) \
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

    #-----------------------------------------------------------------------
    def getSubscriptType(self, inst, subs):
        assert isinstance(subs, pyPEG.Symbol)
        assert subs.__name__ == "SUBSCRIPT"
        line = getBestLineNumberForExpresion(subs)
        #subs.what = IDENT, -1, (re.compile(r"["),[IDENT,INT],re.compile(r"]"))
        _name = ast2str(subs.what[0])
        _pt = self.mdl.proctypes[inst.proctype]
        try:
            array = self.getVarDeclaration(inst, _name)
        except:
            raise Error("Undeclared variable \'"+_name+"\' at <"+line+">.")
        _subs = clearAst(subs.what)
        _idx = 1 # the next subscription
        _type = array.type
        for _idx in range(1,len(_subs)):
            # check we are subscribing an array  
            if _type.type != Types.Array:
                raise Error( "Error at line <"+line+"> Can't subscribe to \'"\
                           + _name \
                           + "\' because it is not an array.")
            #check index is inside range
            (_l,_u) = self.getIndexRange(inst
                                        , ast2str(_subs[_idx])
                                        , ast2str(subs))
            if int(_type.start) > _u or int(_type.end) < _l:
                 raise Error( "Subscription out of range at <" + line + ">,"\
                            + "inside \'" + ast2str(subs) + "\'.")
            elif int(_type.start) > _l or int(_type.end) < _u:
                raise Error( "While checking instance <" + inst.name\
                             + ">: subscription <" + ast2str(_subs[_idx])\
                             + "> may go out of range"
                           , "\'"+ ast2str(subs) + "\'."
                           , "line <" + line + "> of your model file.")

            _type = _type.domain

        return _type.type

    #-----------------------------------------------------------------------
    def getIndexRange(self, inst, idx, ctxt='Some where'):
        assert isinstance(inst, Parser.Instance)
        assert isinstance(idx, str) or isinstance(idx, unicode)
        try:
            # if it's an integer then we get it else raises an exception.
            _i = int(idx)
            return (_i,_i)
        except:
            _t = self.tryToGetType(inst, idx, ctxt)
            if _t != Types.Int:
                raise Error("Can't index an array with <" + idx + ">, as"\
                           +" it's not of integer type. At " + ctxt)
            else:
                # get and return declared range for the variable
                _vt = self.typetable[inst.name][idx]
                assert _vt.domain[0] != None and _vt.domain[1] != None
                return (int(ast2str(_vt.domain[0])),\
                        int(ast2str(_vt.domain[1])))
        
    #-----------------------------------------------------------------------
    def getVarDeclaration(self, inst, varname):
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
            if ast2str(x) == ctxname:
                break
            i += 1
        
        # can't find the varname in this instance        
        if i == len(pt.contextvars):
            raise UndeclaredError(varname)

        instanced = ast2str(inst.params[i], False)
        # instanced is an instance name
        if vname != "":
            newinst = self.mdl.instances[instanced]
            return self.getVarDeclaration(newinst, vname)

        # instanced is an variable name
        assert "." in instanced
        newiname, newvname = instanced.split(".",1)
        newinst = self.mdl.instances[newiname]
        return self.getVarDeclaration(newinst, newvname)


    #-----------------------------------------------------------------------
    def getSynchroNamesList(self):
        _set = set([])
        for inst in self.mdl.instances.itervalues():
            pt = self.mdl.proctypes[inst.proctype]
            n = len(pt.contextvars)
            for e in inst.params[n::]:
                _set.add(ast2str(e))
        return list(_set)


    #-----------------------------------------------------------------------
    def getEventType(self,inst,ast):
        assert isinstance(ast, pyPEG.Symbol)
        assert ast.__name__ == "EVENT"
        ev = ast.what[1]
        sv = ast2str(ev)
        if not '.' in sv:

            lst = self.getSynchroNamesList()
            if sv in lst:
                return Types.Bool
               
            line = getBestLineNumberForExpresion(ast)
            raise Error( "Error at <" + line + ">. There can't be no event" \
                         + " called \'" + ast2str(ast) + "\'.")               
        else:
            ei,ev = sv.split('.', 1)
            try:
                einst = self.mdl.instances[ei]
                ept = self.mdl.proctypes[einst.proctype]
                salst = [ast2str(x) for x in ept.synchroacts]
                elist = [ x.name for x in ept.faults + ept.transitions \
                          if x.name not in salst]
                if not ev in elist:
                    line = getBestLineNumberForExpresion(ast)
                    raise Error("Error in event \'" + ast2str(ast) + "\', at <"\
                                 + line + ">. No event named \'" \
                                 + ev + "\' in instance \'" + ei + "\'.")
            except KeyError as e:
                line = getBestLineNumberForExpresion(ast)
                raise Error( "Error in event \'" + ast2str(ast) + "\', at <" \
                             + line + ">. \'" + ei \
                             + "\' doesn't name an instance.")
            return Types.Bool
            
        assert False # never come out here

    #-----------------------------------------------------------------------
    def tryToGetType(self, inst, elem, context):
        name = ast2str(elem).split(" ")[0] #split in case its a SUBSCRIPT
        ctxt = ast2str(context)
        line = getBestLineNumberForExpresion(elem)
        try:
            t = self.getTypeFromTable(inst, unicode(name))
            return t
        except UndeclaredError:
            raise Error( "Undeclared variable \'" + name + "\' at <" \
                       + line + ">, inside expresion \'" + ctxt + "\'.")

    #-----------------------------------------------------------------------
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
            if int(ast2str(_set.what[0])) > int(ast2str(_set.what[2])):
                raise Error( "Empty range \'" + ast2str(_set) 
                             + "\' at <" + str(line) + ">.")
            if t != Types.Int:
                ts = Types.Types[t]
                raise Error( "Can't check inclusion of an element " \
                             + "of type <" + ts \
                             + "> in a range, in \'" + ast2str(ast) \
                             + "\' at <" + line + ">.")
        else:
            assert False # never come out here
        return Types.Bool


#==============================================================================#
# TESTING =====================================================================#
#==============================================================================#


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

# TODO I think that redeclared is not a word in any language. Change it if so

