#===============================================================================
# Module: Compiler.py
# Author: Raul Monti
# F A LL U T O 2.0
# Mon 27 Jan 2014 05:55:42 PM ART
#===============================================================================
#
from Parser import *
import Parser
from Debug import *
import Debug
from Types import *
import Types
from Utils import *
from Utils import ast2lst, ast2str
import Utils
from Checker import *
import Checker
import Mejoras
# TODO join both modules Compiler and Compiled
from Compiled import Compiled

#
#===============================================================================

# FIXME problema con ! var in {,,,}


# THE COMPILER =================================================================

class Compiler(object):
    """
        Compiler objects allow you to compile a Falluto2.0 system parsed by
        the parse function in the Parser.py module into a valid NuSMV system
        description. The system must be correct in order to succeed, use the
        Checker.py module to check system correctness.
        The saveToFile method in this class allows you to save the compiled
        system into a file in order to check it with NuSMV.
    """
    # Global instance name? Lets say the parallel composition system name?
    __glinst = "Glob#inst"
    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)
    __stfv = "stop#Faults" #boolean variable for stoping fault ocurrence in
                           #finitely many faults mechanism
    __atmostCount = "atmost#count" #for atmost meta-properties
    __ensureCount = "ensure#count" #for ensure meta-properties
    __ensureBlock = "ensure#block" #for ensure meta-properties

    # to export
    _actvar = __actvar
    _dkact  = __dkact

    #===========================================================================
    def __init__(self):
        self.compiled = Compiled()
        self.sys                = None
        self.ctable             = {}    # 3 levels map: inst->var->compiledVar
        self.varset             = set([])   # all program variables set.
        self.syncToTrans        = {}    # read method fillSyncTransDict()
        self.gtctable           = {}    # read method fillGTCTable
        self.transdict          = {}    # read method fillTransCompilingDict
        self.synchroMap         = {}    # read method fillTransCompilingDict
        self.synchrodict        = {}    # read method fillTransCompilingDict

    #===========================================================================
    def compile(self, system):
        assert isinstance(system, Parser.Model)
        self.sys = system

        # fill tables
        self.fillSyncTransDict()
        self.fillVarSet()
        self.fillVarCompilationTable()
        self.fillTransCompilingDict()
        self.fillGTCTable()

        # compile the system and save it in self.compiledstring
        self.compileSystem()

    #===========================================================================
    def fillVarSet(self):
        """
            Fill in self.varset with every variable name to be in the
            compiled program. (those declared in VAR section)
        """
        self.varset.add(Compiler.__actvar)
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # fault active variables
            for f in [x for x in pt.faults if x.type != Types.Transient]:
                self.varset.add(self.compileFaultActive(inst.name, f.name))
            # common variables
            for var in pt.localvars:
                if not var.type.type == Types.Array:
                    self.varset.add(self.compileLocalVar(inst.name, var.name))
                else:
                    for v in self.arrayToVars(var):
                        self.varset.add(self.compileLocalVar(inst.name, v))

            # instance program counters
            self.varset.add(self.compileIPC(inst.name))


    #===========================================================================
    def arrayToVars(self, array):
        """
            Get an array type VarDeclaration and return a list with variable
            names representing each position of the array.
        """
        assert isinstance(array, Parser.VarDeclaration)
        assert array.type.type == Types.Array
        _result = [array.name]
        _t = array.type
        while _t.type == Types.Array:
            _auxres = []
            for l in range(0,len(_result)):
                for _i in range(int(_t.start), int(_t.end)+1):
                    _auxres.append(_result[l]+'['+str(_i)+']')
            _result = _auxres
            _t = _t.domain
        return _result

    #===========================================================================
    def fillVarCompilationTable(self):
        """
            Fill in self.ctble
            ctble is a 2 level map: inst name -> var name -> compiled var name
        """
        # Compiler.__glinst is the 'namespace' for varibales outside
        # instances name spaces (for example in properties declarations)
        self.ctable[Compiler.__glinst] = {}
        # local vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            self.ctable[inst.name] = {}
            for lv in pt.localvars:
                self.ctable[inst.name][lv.name] = \
                    self.compileLocalVar(inst.name, lv.name)
                # global instance for properties and contraints compilation
                self.ctable[Compiler.__glinst][inst.name + '.' + lv.name] = \
                    self.ctable[inst.name][lv.name]
                # Enumerated values (the ones declared inside ENUMs)
                if lv.type == Types.Symbol:
                    for x in lv.domain:
                        self.ctable[inst.name][x] = self.compileSymbValue(x)
                        # global instance again
                        self.ctable[Compiler.__glinst][x] = \
                            self.compileSymbValue(x)

        # context vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for i in range(0,len(pt.contextvars)):
                scv = ast2str(pt.contextvars[i])
                siv = ast2str(inst.params[i])
                # if the parameter is an instance reference
                if siv in self.sys.instances:
                    pinst = self.sys.instances[siv]
                    ppt = self.sys.proctypes[pinst.proctype]
                    for x in ppt.localvars:
                        vname = scv + '.' + x.name
                        self.ctable[inst.name][vname] = \
                            self.ctable[pinst.name][x.name]
                # if it's another instance's var reference
                elif '.' in siv:
                    ii,vv = siv.split('.',1)
                    self.ctable[inst.name][scv] = self.ctable[ii][vv]
                # else it's a boolean value or an integer
                # TODO quizas no deberia permitir esto
                else:
                    assert isBool(siv) or isInt(siv)
                    self.ctable[inst.name][scv] = self.compileBOOLorINT(siv)

        # DEFINEs
        for d in self.sys.defs.itervalues():
            dname = ast2str(d.dname)
            compd = self.compileDefine(dname)
            self.ctable[Compiler.__glinst][dname] = compd

            for inst in self.sys.instances.itervalues():
                iname = inst.name
                try:
                    aux = self.ctable[iname][dname]
                except:
                    self.ctable[iname][dname] = compd



    #===========================================================================
    def fillSyncTransDict(self):
        """
            @ NOT COMPILED NAMES
             
            @ Fill self.syncToTrans map with synchro names as keys and a list, 
            with the sincronized transitions for each instance, as value.
        """
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            i = 0
            # for each synchro action
            for sname in [ast2str(x) for x in inst.params[n::]]:
                try:
                    table = self.syncToTrans[sname]
                except:
                    self.syncToTrans[sname] = {}

                # get synchronized action name from the proctype
                ptstname = ast2str(pt.synchroacts[i])
                for t in pt.transitions:
                    if t.name == ptstname:
                        try:
                            self.syncToTrans[sname][inst.name].append(t)
                        except:
                            self.syncToTrans[sname][inst.name] = [t]
                i += 1



# TODO termine de revisar hasta aca, y aparentemente esta todo en orden

    #===========================================================================
    def fillTransCompilingDict(self):
        """
            Fill in self.transdict and self.synchrodict

            self.transdict[iname][tname][tpc] \
                 -> (trans_compiled_name, [trans_enable_conditions], \
                        [trans_postconditions])
            
            self.synchrodict[stname] \
                -> [(trans_compiled_name, [trans_enable_conditions], \
                        [trans_postconditions])]            
            
            @ trans_postcondition doesn't include action next value.
        """

        # not synchronised transitions
        for inst in self.sys.instances.itervalues():
            iname = inst.name
            self.transdict[iname] = {}
            pt = self.sys.proctypes[inst.proctype]
            for t in pt.transitions:
                if not t.name in pt.synchroacts:
                    if not t.name in self.transdict[iname]:
                        self.transdict[iname][t.name] = {}
                    # ENABLE CONDITION:
                    elst = self.getPreList(iname, t)
                    
                    # POSCONDITION
                    plst, vset = self.getPosList(iname, t)
                    vset.add(Compiler.__actvar)
                    uvset = self.varset - vset
                    for v in uvset:
                        plst.append(self.compileNextRef(v) + ' = ' + v)
                    
                    #ADD TO DICT
                    tcname = self.compileTransitionName(iname, t.name)
                    self.transdict[iname][t.name][t.pc] = (tcname, elst, plst)

        # Synchronised transitions
        for (stname,slst) in self.syncToTrans.iteritems():
            self.synchrodict[stname] = []
            # Each element in the cartesian product represent a possible 
            # escenary of synchronization between instances that synchronice 
            # through stname. Each scenary is distinguished by the synchro
            # program counter (spc variable).
            cp = self.synchroCartesianProduct(slst)
            csname = self.compileSynchroAct(stname)

            for e in cp:
                elst = []
                plst = []
                vset = set([Compiler.__actvar])
                for iname, t in e:
                    # save information to map 
                    elst += self.getPreList(iname,t)
                    auxplst, auxvset = self.getPosList(iname, t)
                    plst += auxplst
                    vset = vset.union(auxvset)

                uvset = self.varset - vset

                # Add unchanged variables to post-condition
                for v in uvset:
                    plst.append(self.compileNextRef(v) + ' = ' + v)

                # ADD TO DICT
                self.synchrodict[stname].append((csname,elst,plst))



    #===========================================================================
    def synchroCartesianProduct(self, llst):
        """
            @ NOT COMPILED VALUES
            @ Build a cartesian product from each value in the self.syncToTrans
            map, (should be passed as llst).
        """
        result = [[]]
        for i,tl in llst.iteritems():
            aux = []
            for t in tl:
                for r in result:
                    aux.append( r + [(i,t)])
            result = aux
        return result


    #===========================================================================
    def getPreList(self, iname, trans):
        inst = self.sys.instances[iname]
        pt = self.sys.proctypes[inst.proctype]
        elst = []

        # STOP faults that disable this transitions
        for f in [x for x in pt.faults if x.type == Types.Stop]:
            if f.affects == [] or \
                trans.name in [ast2str(x) for x in f.affects]:
                elst.append(self.neg(
                    self.compileFaultActive(inst.name, f.name)))
        # Transition enable condition
        assert trans.pre != None
        elst.append(self.compileAST(inst.name, trans.pre))
        
        return elst
        

    #===========================================================================
    def getPosList(self, iname, trans):
        plst = []
        changed = set([])
        # Transition postcondition
        for p in trans.pos:
            cref = self.compileLocalVar(iname, ast2str(p[0],False))
            changed.add(cref)
            _u = ''
            if p[1].__name__ == "SET" or p[1].__name__ == "RANGE":
                _u = 'in'
            else:
                _u = '='
            plst.append( self.compileNextRef(cref) \
                         + ' ' + _u + ' ' \
                         + self.compileAST(iname, p[1]))
        # program counter
        plst.append(self.compileNextRef(self.compileIPC(iname)) + ' = ' \
            + str(trans.pc))
        changed.add(self.compileIPC(iname))
        # Variables that wont change
        assert changed.issubset(self.varset)
        return plst, changed
    
        
    #===========================================================================
    def fillGTCTable(self):
        """ 
            @  Fill the transitions global compilation table. This table is used
            to compile events in propositional formulas of properties and
            contraints. It maps the name of normal and faulty transitions as you
            find it outside proctypes declarations, into the correct compiled 
            value.
            
            @  self.gtctable is a dictionary: fault/trans name -> compiledvalue
        """
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # Faulty transitions
            for f in pt.faults:
                self.gtctable[inst.name + '.' + f.name] \
                    = self.compileFaultActionVar(inst.name, f.name)
            # Normal not synchronous transitions
            for t in pt.transitions:
                if not t.name in [ast2str(x) for x in pt.synchroacts]:
                    self.gtctable[inst.name + '.' + t.name] \
                        = self.compileTransitionName(inst.name, t.name)

        # Normal synchronous transitions
        for stname in self.syncToTrans.iterkeys():
            self.gtctable[stname] = self.compileSynchroAct(stname)

    #===========================================================================
    def compileSystem(self):
        """
            Compiles the whole system except for the properties.
        """
        self.buildDefines()
        self.buildVarSection()
        self.buildInitSection()
        self.buildTransSection()
        self.buildContraints()
        # build properties and queue them into the propertie vector
        self.buildProperties()


    #===========================================================================
    def buildDefines(self):
        _idx = 0
        for d in self.sys.defs.itervalues():
            cdname = self.compileDefine(ast2str(d.dname))
            self.compiled.adddef( "Defintion <"+str(_idx)+">"
                                , ""
                                , "DEFINE " + cdname + " := " \
                                  + self.compileAST(Compiler.__glinst,d.dvalue)\
                                  + ";"
                                )
            _idx += 1

    #===========================================================================
    def buildVarSection(self):
        # ACTION VARIABLE
        lst = set([]) 
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # faults
            for fault in pt.faults:
                lst.add(self.compileFaultActionVar(inst.name, fault.name))
            # transitions
            for act in pt.transitions:
                if not act.name in [ast2str(x) for x in pt.synchroacts]:
                    lst.add(self.compileTransitionName(inst.name, act.name))
            n = len(pt.contextvars)
            # Synchro actions
            for act in [ast2str(x) for x in inst.params[n::]]:
                lst.add(self.compileSynchroAct(act))
            # BYZ effects
            for f in pt.faults:
                if f.type == Types.Byzantine:
                    lst.add(self.compileByzEffect(inst.name, f.name))
        # deadlock action
        lst.add(Compiler.__dkact)
        # save
        self.compiled.addvar( Compiler.__actvar
                            , "The 'last action' variable"
                            , Compiler.__actvar + ':' + self.compileSet(lst)+';'
                            )

        # LOCAL VARIABLES
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                vname = self.ctable[inst.name][var.name]
                if var.type == Types.Bool:
                    #FIXME muy choto este parche, corregir cuando haya tiempo
                    if var.isarray:
                        self.compiled.addvar( vname, "", vname + " : array "\
                            + str(var.range[0]) + ".." + str(var.range[1])\
                            + " of boolean;")
                    else:
                        self.compiled.addvar(vanme, "", vname + ":boolean;")
                else:
                    self.compiled.addvar(vname, "",
                        self.compileAST( inst.name, var.pypeg, True, pb=False)\
                        + ";")

        # FAULT ACTIVITY VARIABLES
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in [x for x in pt.faults if x.type != Types.Transient]:
                name = self.compileFaultActive(inst.name, f.name)
                self.compiled.addvar( name, "", name + ":boolean;")

        # INSTANC PROGRAM COUNTERs
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            vname = self.compileIPC(inst.name)
            self.compiled.addvar(vname, "", vname \
                + " : 0.." + str(max(len(pt.transitions)-1,0)) + ";")

    #===========================================================================
    def buildProperties(self):
    # TODO this should be completely changed (NB and FMF) ?????
        if Types.Checkdk in [x.type for x in self.sys.options.itervalues()]:
            self.buildDkCheckPropertie()
    
        for p in self.sys.properties.itervalues():
            formula = self.replaceEvents(p.formula)
            pRepr = ""
            if p.explain:
                pRepr = p.explain + ": "

            if p.type == Types.Ctlspec:
                pRepr += "CTLSPEC "+putBracketsToFormula(p.formula,False) 
                pComp = "CTLSPEC "+self.compileAST(Compiler.__glinst, formula)
                self.compiled.addprop(p.name, pRepr, pComp)
            elif p.type == Types.Ltlspec:
                pRepr += "LTLSPEC "+putBracketsToFormula(p.formula,False) 
                pComp = "LTLSPEC "+self.compileAST(Compiler.__glinst, formula)
                self.compiled.addprop(p.name, pRepr, pComp)
            elif p.type == Types.Nb:
                pRepr = p.explain + ': ' + "NORMAL_BEAHAIVIOUR "\
                    +putBracketsToFormula(p.formula,False)
                pComp = self.compileUnknownPropertie(p)
                self.compiled.addprop(p.name, pRepr, pComp)
            elif p.type == Types.Fmf or p.type == Types.Fmfs:
                # FIXME it would be cleaner to set the representation of the
                # the property at parser level and not here.
                self.compiled.addprop(p.name
                    , pRepr + "FINITELY_MANY_FAULT/S (" \
                      + self.symbolSeparatedTupleString( \
                      [ast2str(x) for x in p.params], False, False, ',') + ")"\
                      + ' -> ' + putBracketsToFormula(p.formula,False)
                    , self.compileUnknownPropertie(p))
            elif p.type == Types.Atmost:
                self.compiled.addprop(p.name
                    , pRepr + "ATMOST (" + ast2str(p.limit) + ','\
                    + self.symbolSeparatedTupleString( 
                          [ast2str(x) for x in p.params], False, False, ',')\
                    + ") -> " + ast2str(p.formula)
                    , self.compileUnknownPropertie(p))
            elif p.type == Types.Ensure:
                self.compiled.addprop(p.name
                    , pRepr + "ENSURE (" + ast2str(p.limit) + ','\
                    + self.symbolSeparatedTupleString( 
                          [ast2str(x) for x in p.actions], False, False, ',')\
                    + ") WITHOUT ("\
                    + self.symbolSeparatedTupleString( 
                          [ast2str(x) for x in p.params], False, False, ',')
                    + ") -> " + ast2str(p.formula)
                    , self.compileUnknownPropertie(p))
            else:
                raise Error("bad type for propertie: " + str(p.type))

    #===========================================================================
    def compileUnknownPropertie(self, p):
        """
        """
        _result = ""
        if p.formula.__name__ == "CTLEXP":
            _result =  "CTLSPEC " + self.compileAST(Compiler.__glinst,p.formula)
        elif p.formula.__name__ == "LTLEXP":
            _result = "LTLSPEC " + self.compileAST(Compiler.__glinst,p.formula)
        else:
            assert False
        return _result

    #===========================================================================
    def buildDkCheckPropertie(self):
        self.compiled.addprop(
            "NEVER FALLS IN DEADLOCK",
            "DEADLOCK CHECK",
            "CTLSPEC AX AG " + Compiler.__actvar + " != " + Compiler.__dkact)

    #===========================================================================
    def buildContraints(self):

        if not Types.WFDisable in \
            [x.type for x in self.sys.options.itervalues()]:
            self.buildWeakFairContraint()
        if not Types.FFDisable in \
            [x.type for x in self.sys.options.itervalues()]:
            self.buildFaultFairContraint()
        for c in self.sys.contraints.itervalues():
            self.buildNormalContraint(c)

# TODO revisar que pasa con la sincronizacion cuando no se usa la variable de 
# sincronizacion en el proctype mas alla de tenerla como parametro.
    #===========================================================================
    def buildWeakFairContraint(self):
        """ SYSTEM - MODULE FAIRNESS
            Weak fairness para modulos. Un modulo que esta infinitamente 
            habilitado para realizar alguna accion normal, debe ser atendido 
            infinitamente a menudo. Un modulo puede entrar en deadlock cuando 
            todas sus guardas son inhabilitadas, pero puede salir del mismo a
            partir de cambios en el resto del sistema.
            Pedimos fairness para las acciones del modulo o para el estado de
            deadlock del modulo, de esta manera si el modulo nunca cae en
            dedalock (siempre esta habilitado para realizar una accion normal)
            entonces en algun momento va a ser atendido.
        """
        for inst in self.sys.instances.itervalues():
            actVec = []
            dkVec = []
            pt = self.sys.proctypes[inst.proctype]

            # not synchro transition
            slst = [ast2str(x) for x in pt.synchroacts]
            for t in pt.transitions:
                if not t.name in slst:
                    # put names into the list
                    actVec.append(self.transdict[inst.name][t.name][t.pc][0])
                    # transitions pre negations (module deadlock condition)
                    pre = self.transdict[inst.name][t.name][t.pc][1]
                    assert pre != []
                    dkVec.append(self.getPreNegation(pre))    
                    
            # synchro transition 
            n = len(pt.contextvars)
            i = 0
            for stname in inst.params[n::]:
                stname = ast2str(stname)
                sa = ast2str(pt.synchroacts[i])                
                if sa in [t.name for t in pt.transitions]:
                    # put names into the list
                    actVec.append(self.compileSynchroAct(stname))
                    # transitions pre negations (module deadlock condition)
                    ss = self.synchrodict[stname]
                    auxvec = []
                    # all the possible synchronizations must be blocked
                    for e in ss:
                        pre = e[1]
                        assert pre != []
                        auxvec.append(self.getPreNegation(pre))
                    dkVec.append(self.symbolSeparatedTupleString(auxvec))

            #if module hasn't got any actions:
            if actVec == []:
                continue

            dkString = self.symbolSeparatedTupleString( dkVec, False, False)

            actString = Compiler.__actvar + " in " + self.compileSet(actVec)

            self.compiled.addconstr( "@WFC#"+inst.name
                , "Falluto Weak Fairness constraint"
                , "FAIRNESS " + (self.symbolSeparatedTupleString( \
                  [dkString, actString], False, False, '|')))

    #===========================================================================
    def getPreNegation(self, prelst):
        prevec = []
        for p in prelst:
            prevec.append(self.neg(p))
        return self.symbolSeparatedTupleString(prevec, False, False, amp = '|')

    #===========================================================================
    def buildFaultFairContraint(self):
        # FAULT - SYSTEM FAIRNESS
        # Para evitar que las fallas se apoderen del sistema, nos restringimos
        # a trazas en las que siempre eventualmente ocurra alguna transicion
        # normal (no de falta). Por defecto se usa esta configuracion.
      
        actionset = set([Compiler.__dkact])
        for i in self.sys.instances.itervalues():
            pt = self.sys.proctypes[i.proctype]
            for t in pt.transitions:
                if t.name not in [ast2str(x) for x in pt.synchroacts]:
                    actionset.add(self.transdict[i.name][t.name][t.pc][0])

        for e in self.syncToTrans.iterkeys():
            actionset.add(self.compileSynchroAct(e))

        self.compiled.addconstr("@FSFC"
            , "Falluto Fault-System fairness constraint"
            , "FAIRNESS (" + Compiler.__actvar + " in " + \
              self.compileSet(list(actionset)) + ")")



    #===========================================================================
    def buildNormalContraint(self, c):
        if c.type == "FAIRNESS":
            param = self.replaceEvents(c.params[0])
            self.compiled.addconstr( ""
                , "FAIRNESS CONSTRAINT"
                , "FAIRNESS " + self.compileAST(Compiler.__glinst, param))
        elif c.type == "COMPASSION":
            param0 = self.replaceEvents(c.params[0])
            param1 = self.replaceEvents(c.params[1])
            self.compiled.addconstr(""
                , "COMPASSION CONSTRAINT"
                , "COMPASSION ("\
                  + self.compileAST(Compiler.__glinst, param0) + ','\
                  + self.compileAST(Compiler.__glinst, param1) + ")" )
        else:
            assert False
            # TODO is it right to do this type of asserts? what would be the
            # correct way to treat this programming errors?

    #===========================================================================
    def buildInitSection(self):
        lst = []
        flst = ["TRUE"] # 'TRUE' so INIT never gets empty and NuSMV accepts it
        for inst in self.sys.instances.itervalues():
            pk = self.sys.proctypes[inst.proctype]
            # instance initialization
            lst.append(self.compileAST(inst.name, pk.init, True))
            # faults activation var initialization
            for fault in [x for x in pk.faults if x.type != Types.Transient]:
                flst.append( self.compileFaultActive(inst.name,fault.name) \
                            + " = FALSE")
        lst.append(self.symbolSeparatedTupleString(flst, False, False))
        self.compiled.addinit(self.symbolSeparatedTupleString(lst, False, True))

    #===========================================================================
    def buildTransSection(self):
        tlst = []
        # common transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for trans in pt.transitions:
                if not trans.name in [ast2str(x) for x in pt.synchroacts]:
                    self.compiled.addtrans(inst.name+'#'+trans.name
                        , ""
                        , self.buildCommonTrans(inst,pt,trans))
        # synchro transitions
        for trans in self.syncToTrans.iterkeys():
            self.compiled.addtrans('synchro#'+trans
                , ""
                , self.buildSynchroTrans(trans))
        # fault ocurrence transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                self.compiled.addtrans(inst.name+'#'+f.name
                    , ""
                    , self.buildFaultTransition(inst,pt,f))
        # byz effects transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in [x for x in pt.faults if x.type == Types.Byzantine]:
                self.compile.addtrans( inst.name+'#bizEfect#'+f.name
                    , ""
                    ,self.buildByzantineTrans(inst,pt,f))
        # deadlock transitions
        self.compiled.addtrans("deadlock#transition"
            , "@ DEADLOCK TRANSITION"
            , self.buildDeadLockTrans())

    #===========================================================================
    def buildCommonTrans(self, inst, pt, t):
    
        tcname, pre, pos = self.transdict[inst.name][t.name][t.pc]
    
        tlst = []
        # set next action to this transition
        tlst.append( self.compileNextRef(Compiler.__actvar) + " = " + tcname)

        # pre and pos conditions
        tlst += pre + pos

        return self.symbolSeparatedTupleString(tlst, False, False)


    #===========================================================================
    def buildSynchroTrans(self, strans):
    
        result = []
        sync = self.synchrodict[strans]
        for (cname, pre, pos) in sync:
            stlst = []
            # set next action to this transition
            stlst.append(self.compileNextRef(Compiler.__actvar) + " = " + cname)

            stlst += pre + pos
            
            result.append(self.symbolSeparatedTupleString(stlst, False, False))
        # RETURN
        return self.symbolSeparatedTupleString(result, False, True, amp = '|')
        


    #===========================================================================    
    def buildFaultTransition(self, inst, pt, f):
        ftlst = []
        # ACTION
        vset = set([])
        # set next action to this transition
        vset.add(Compiler.__actvar)
        ftlst.append(self.compileNextRef(Compiler.__actvar) + " = " \
                    + self.compileFaultActionVar(inst.name, f.name))

        # PRECONDITIONS
        # Not to be active if diferent from transient
        if f.type != Types.Transient:
            ftlst.append(self.neg(self.compileFaultActive(inst.name,f.name)))
        # STOP faults that disable this transitions
        for fault in pt.faults:
            if fault.type == Types.Stop and  fault.affects == []:
                ftlst.append( self.compileFaultActive(inst.name, fault.name) \
                           + " = FALSE")
        # Transition enable condition
        if f.pre != None:
            ftlst.append(self.compileAST(inst.name, f.pre))

        # POSTCONDITIONS
        # Transition postcondition
        for p in f.pos:
            cref = self.compileLocalVar(inst.name, ast2str(p[0],False))
            vset.add(cref)
            ftlst.append( self.compileNextRef(cref) + ' ' + ast2str(p[1]) + ' ' \
                        + self.compileAST(inst.name, p[2]))
        # fault activation var
        if f.type != Types.Transient:
            fav = self.compileFaultActive(inst.name, f.name)
            vset.add(fav)
            ftlst.append(self.compileNextRef(fav))
        # Variables that wont change
        assert vset.issubset(self.varset)
        uvset = self.varset - vset
        for v in uvset:
            ftlst.append(self.compileNextRef(v) + ' = ' + v)
        # RETURN
        return self.symbolSeparatedTupleString(ftlst, False, False)



    #===========================================================================
    def buildByzantineTrans(self, inst, pt, f):
        thistransvect = []
        exceptSet = set([])
        # set action to this transition
        thistransvect.append("next(" + Compiler.__actvar + ") = " +\
            self.compileByzEffect(inst.name, f.name))
        exceptSet.add(Compiler.__actvar)
        # Byz fault must be active
        thistransvect.append(self.compileFaultActive(inst.name,f.name))
        for e in f.affects:
            #con agregarlas a la lista de excepcion ya me aseguro de que no se
            #defina el proximo valor para la variable y por lo tanto NuSMV le
            #asigne un valor aleatorio dentro de su dominio. 8-)
            exceptSet.add(self.compileLocalVar(inst.name,ast2str(e)))
        #everithing else:
        for v in self.varset - exceptSet:
            thistransvect.append("next(" + v + ") = " + v)
        return self.symbolSeparatedTupleString(thistransvect,False,False)


    #===========================================================================
    def buildDeadLockTrans(self):
        # TODO usar el mapa con precondiciones de las trans para esta transicion
        result = []
        # set action to dead lock
        result.append( "next(" + Compiler.__actvar + ") = " + Compiler.__dkact)

        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # negation of local transitions preconditions
            for trans in pt.transitions:
                if trans.name not in [ast2str(x) for x in pt.synchroacts]:
                    tvect = []
                    for p in self.transdict[inst.name][trans.name][trans.pc][1]:
                        tvect.append(self.neg(p))                    
                    result.append( self.symbolSeparatedTupleString( \
                                   tvect, False, False, '|'))

        # negation of synchro transitions preconditions
        for sync in self.synchrodict.itervalues():
            for cs, pre, pos in sync:
                syncvect = []
                for p in pre:
                    syncvect.append(self.neg(p))
                result.append(self.symbolSeparatedTupleString(syncvect, \
                    False, False, '|'))
        
        # nothing else changes
        for v in self.varset - set([Compiler.__actvar]):
            result.append( "next(" + v + ") = " + v)

        return self.symbolSeparatedTupleString(result, False, False)
    
    #===========================================================================
    """ Get stop faults that affect action in instance.

        @instance:
            Instance class instance where to check
        @action:
            Transition name to check
        @return:
            list of stop faults that affect the transition
    """
    def getStopFaultsForAction(self, inst, act):
        faultlist = []
        pt = self.sys.proctypes[inst.proctype]
        for f in [x for x in pt.faults if x.type == Types.Stop]:
            # action != f.name so global stop faults dont stop them selves
            # don't know if it's right to do so.
            if (act.name in [ast2str(x) for x in f.affects]) or (f.affects == []) \
                and act.name != f.name:
                faultlist.append(f)
        return faultlist

    #===========================================================================
    def neg(self, string):
        if string == None or string == "":
            return ""
        else:
            return "!(" + string + ")"


    #===========================================================================
    def symbolSeparatedTupleString(self, array, parent = False, enter=False,\
                                     amp = '&'):
        parentopen = ""
        parentclose = ""
        amperson = " " + amp + " "
        if parent:
            parentopen = "("
            parentclose = ")"
        if enter:
            amperson = amperson + "\n"

        marray = []
        for elem in array:
            if str(elem) != "":
                marray.append(elem)
        if marray == []:
            return ""
        elif len(marray) == 1:
            return str(marray[0])
        else:
            string = parentopen + "(" + str(marray[0]) + ")"
            for elem in marray[1::]:
                string += amperson + "(" + str(elem) + ")"
            string += parentclose
            return string

    #===========================================================================
    # COMPILATION METHODS ======================================================
    #===========================================================================
    def compileLocalVar(self, iname, vname):
        return "lvar#" + iname + "#" + vname

    #===========================================================================
    def compileSymbValue(self, x):
        return "sv#" + x

    #===========================================================================
    def compileFaultActionVar(self, iname, fname):
        return "fault#" + iname + '#' + fname

    #===========================================================================
    def compileTransitionName(self, iname, tname):
        return "trans#" + iname + '#' + tname

    #===========================================================================
    def compileSynchroAct(self, saname):
        return "synchro#" + saname

    #===========================================================================
    def compileByzEffect(self, iname, fname):
        return "byzE#" + iname + '#' + fname

    #===========================================================================
    def compileSet(self, _set):
        lst = list(_set)
        if lst == []:
            return "{}"
        string = "{ " + str(lst[0])
        for x in lst[1::]:
            string += ', ' + str(x) 
        return string + '}'

    #===========================================================================
    def replaceEvents(self, ast):
        if isinstance(ast, pyPEG.Symbol):
            ps = pyPEG.Symbol(ast.__name__,[])
            if ast.__name__ == "EVENT":
                ps.what.append(unicode('('))
                ps.what.append(unicode(Compiler.__actvar)) 
                ps.what.append(unicode(" = "))
                ps.what.append(unicode(self.gtctable[ast2str(ast.what[1])]))
                ps.what.append(unicode(')'))
                return ps
            else:
                for elem in ast.what:
                    ps.what.append(self.replaceEvents(elem))
                return ps
        elif isinstance(ast, list):
            lst = []
            for elem in ast:
                lst.append(self.replaceEvents(elem))
            return lst
        else:
            return ast
        assert False #never come out here
            
    #===========================================================================

    def compileAST(self, iname, ast, space = True, pb = True):
        """ Get a pyPEG ast structure with some expresion and return a string
            representing the information in that structure, but with 
            symbols replaced to its compiled values as should apear in the
            NuSMV model file.
            @input iname: the instance name to which de expresion in ast 
                          corresponds, (needed for compiling the symbols).
            @input ast  : the ast structure to compile.
            @input pb   : if we wan't to plave brackets to ensure formulas 
                          operators presedence.
        """
        if ast == None:
            return ""
        if pb:
            # ast = putBracketsAsList(ast) FIXME we may need to do this
            # if NuSMV desagrees with us :S.
            pass
        sp = ""
        if space:
            sp = " "
        string = ""
        # we don't want spaces nor comments
        for x in ast2lst(ast,['BL','COMMENT']):
            try:
                string += self.ctable[iname][x] + sp
            except:
                # FIXME feo parche :s
                if x == '%':
                    string += "mod"
                elif x == 'True':
                    string += 'TRUE'
                elif x == 'False':
                    string += 'FALSE'
                else:
                    string += x
                if x != '!' and x != '-':
                    string += sp
        return string

    #===========================================================================
    def compileFaultActive(self, iname, fname):
        return "factive#" + iname + '#' + fname

    #===========================================================================
    def compileNextRef(self, ref):
        return "next(" + ref + ")"

    #===========================================================================
    def compileBOOLorINT(self, value):
        return ast2str(value)

    #===========================================================================
    def compileDefine(self, name):
        return "def#" + str(name)

    #===========================================================================
    def compileIPC(self, iname):
        return "ipc#" + iname


    #===========================================================================
    # BUILD THE MODEL AND WRITE IT TO A FILE ===================================
    #===========================================================================

    def buildModel(self, pname="", fpath=""):
        """ Build the system to model check property with name pname in NuSMV
            and write it to file.
            @Warning: you need to compile the model first.
        """
        
        if pname:
            _addvar = []
            _addinit = ""
            _addtrans = ""
            _prop = self.sys.properties[pname]
            assert _prop != None
            # common properties:
            if _prop.type == Types.Ctlspec or _prop.type == Types.Ltlspec:
                self.compiled.buildModel(props=[pname])
            # normal behaiviour meta-properties:
            elif _prop.type == Types.Nb:
                _addtrans = self.getNBtransition()
            # finitely many faults meta-properties:
            elif _prop.type == Types.Fmf or _prop.type == Types.Fmfs:
                _addvar = [self.__stfv + ': boolean;']
                _addinit = '& !' + self.__stfv
                _addtrans = self.getFMFtransition(_prop)
            # atmost meta-properties:
            elif _prop.type == Types.Atmost:
                _addvar =\
                    [self.__atmostCount + ': 0..' + ast2str(_prop.limit) + ';']
                _addinit = '& ' + self.__atmostCount + ' = 0'
                _addtrans = self.getATTtransition(_prop) 
            # ensure meta-properties:
            elif _prop.type == Types.Ensure:
                _addvar =\
                    [ self.__ensureCount + ': 0..' +ast2str(_prop.limit) +';'
                    , self.__ensureBlock + ': boolean;']
                _addinit = '& (' + self.__ensureCount + ' = 0) & !'\
                         + self.__ensureBlock
                _addtrans = self.getEtransition(_prop)                
            else:
                assert TypeError(_prop.type)

            self.compiled.buildModel( _addvar
                                    , _addinit
                                    , _addtrans
                                    ,props=[pname])
        else:
            self.compiled.buildModel()
        # put it in a file at fpath        
        self.compiled.writeSysToFile(fpath)
        
    #===========================================================================
    def getNBtransition(self):
        """ Some kind of properties riquire us to add some extra transitions
            to the compiled model. In this case we are building the extra
            transitions for the case of the normal behaiviour properties.
        """
        _flist = []
        for i in self.sys.instances.itervalues():
            _pt = self.sys.proctypes[i.proctype]
            for _f in _pt.faults:
                _flist.append(self.compileFaultActionVar( i.name, _f.name))
        _addtrans = ""                
        if _flist:
            _addtrans = '& !(' + self.compileNextRef(self.__actvar)\
                      + ' in { ' + _flist[0]
            for _f in _flist[1:]:
                _addtrans += ', ' + _f
            _addtrans += '} )'

        return _addtrans

    #===========================================================================
    def getFMFtransition(self, prop=None):
        """ Some kind of properties riquire us to add some extra transitions
            to the compiled model. In this case we are building the extra
            transitions for the case of the finetely many faults properties.
        """
        # FIXME use compileSet instead of doing it by hand :S
        assert prop!=None
        _addtrans = ""

        _faults = [] # faults clamed by the property
        for _f in prop.params:
            _iname, _fname = ast2str(_f).split('.')
            _faults.append(self.compileFaultActionVar(_iname, _fname))

        if not _faults: # means every fault must finally be stoped
            for i in self.sys.instances.itervalues():
                _pt = self.sys.proctypes[i.proctype]
                for _f in _pt.faults:
                    _faults.append(self.compileFaultActionVar( i.name, _f.name))
                    
        if _faults:
            # there are faults in the model (otherwise the fmf property
            # is useless and we return "").

           _addtrans = '& (!' + self.__stfv + ' | ( ' + self.__stfv + ' & '\
                     + self.compileNextRef(self.__stfv)\
                     + ' & !(' + self.compileNextRef(self.__actvar)\
                     + ' in { ' + _faults[0]
           for _f in _faults[1:]:
               _addtrans += ', ' + _f
           _addtrans += '}))'
           _addtrans += ')'

        return _addtrans

    #===========================================================================
    def getATTtransition(self, prop):
        """ Some kind of properties riquire us to add some extra transitions
            to the compiled model. In this case we are building the extra
            transitions for the case of the atmost meta-properties.
        """
        # FIXME write pseudocode of the transition to explain it.
        assert prop!=None
        _addtrans = ""
        #FIXME duplicated code from getFMFtransition and getNBtransition
        _faults = [] # faults clamed by the property
        for _f in prop.params:
            _iname, _fname = ast2str(_f).split('.')
            _faults.append(self.compileFaultActionVar(_iname, _fname))

        if not _faults: # means every fault must finally be stoped
            for i in self.sys.instances.itervalues():
                _pt = self.sys.proctypes[i.proctype]
                for _f in _pt.faults:
                    _faults.append(self.compileFaultActionVar( i.name, _f.name))
        
        if _faults:
            # there are faults in the model (otherwise the fmf property
            # is useless and we return "").
            _xactvar = self.compileNextRef(self.__actvar)
            _xatcount = self.compileNextRef(self.__atmostCount)
            _addtrans += '& ('\
                      + '( ' + self.__atmostCount + " < " + ast2str(prop.limit)\
                      + ' & (' + _xactvar + ' in '\
                      + self.compileSet(_faults) + ') & '\
                      + _xatcount + ' = ' + self.__atmostCount + '+ 1 )\n| '\
                      + '( ' + self.__atmostCount + " < " + ast2str(prop.limit)\
                      + ' & !(' + _xactvar + ' in '\
                      + self.compileSet(_faults) + ') & '\
                      + _xatcount + ' = ' + self.__atmostCount + ' )\n| '\
                      + '( ' + self.__atmostCount + " = " + ast2str(prop.limit)\
                      + ' & !(' + _xactvar + ' in '\
                      + self.compileSet(_faults) + ') & '\
                      + _xatcount + ' = ' + self.__atmostCount + ' ))'\

        return _addtrans

    #===========================================================================
    def getEtransition(self, prop):
        """ Some kind of properties riquire us to add some extra transitions
            to the compiled model. In this case we are building the extra
            transitions for the case of the 'ensure' meta-properties.
        """
        # FIXME write pseudocode of the transition to explain it.
        assert prop!=None
        _addtrans = ""
        #FIXME duplicated code from getFMFtransition and getNBtransition
        _faults = [] # faults clamed by the property
        for _f in prop.params:
            _iname, _fname = ast2str(_f).split('.')
            _faults.append(self.compileFaultActionVar(_iname, _fname))

        if not _faults: # means every fault must finally be stoped
            for i in self.sys.instances.itervalues():
                _pt = self.sys.proctypes[i.proctype]
                for _f in _pt.faults:
                    _faults.append(self.compileFaultActionVar( i.name, _f.name))
        
        _actions = [] # faults clamed by the property
        for _a in prop.actions:
            _iname, _aname = ast2str(_a).split('.')
            _actions.append(self.compileTransitionName(_iname, _aname))

        if not _actions: # means every fault must finally be stoped
            for i in self.sys.instances.itervalues():
                _pt = self.sys.proctypes[i.proctype]
                for _a in _pt.transitions:
                    _actions.append(self.compileTransitionName(i.name,_a.name))

        if _faults:
            # FIXME decide what to do if there are no faults declared
            # there are faults in the model (otherwise the fmf property
            # is useless and we return "").
            _xactvar = self.compileNextRef(self.__actvar)
            _xencount = self.compileNextRef(self.__ensureCount)
            _addtrans += '& ('\
                      + '( !' + self.__ensureBlock + ' & ' + _xencount\
                      + ' = 0 )\n| '\
                      + '( ' + self.__ensureBlock + ' & ' + self.__ensureCount\
                      + " < "+ast2str(prop.limit) + ' & (' + _xactvar + ' in '\
                      + self.compileSet(_actions)+ ') & !(' + _xactvar+ ' in '\
                      + self.compileSet(_faults) + ') & ' + _xencount + ' = '\
                      + self.__ensureCount + ' + 1 )\n|'\
                      + ' ( ' + self.__ensureBlock + ' & ' + self.__ensureCount\
                      + " < " + ast2str(prop.limit)+ ' & !('+ _xactvar+' in '\
                      + self.compileSet(_actions+_faults) + ') & ' + _xencount\
                      + ' = ' + self.__ensureCount + ')\n|'\
                      + ' (' + self.__ensureBlock + ' & ' + self.__ensureCount\
                      + ' = ' + ast2str(prop.limit) + ' & !('\
                      + self.compileNextRef(self.__ensureBlock) + ') & '\
                      + _xencount + ' = 0))'

        return _addtrans

# TESTING ======================================================================
if __name__ == "__main__":
    
    # Reed file from input
    _file = fileinput.input()
    # Parse file
    _sys = Parser.parse(_file)
    # Check ths system correcteness
    chkr = Checker.Checker()
    chkr.check(_sys)
    # Compile to Nusmv
    _cmpsys = Compile(_sys)
    _cmpsys.writeSysToFile("output.smv",None)
    
