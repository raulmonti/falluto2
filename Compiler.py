#===============================================================================
# Module: Compiler.py
# Author: Raul Monti
# F A LL U T O 2.0
#===============================================================================
#
from Parser import *
import Parser
from Debug import *
import Debug
from Types import *
import Types
from Utils import *
from Utils import _cl, _str
import Utils
from Checker import *
import Checker

import Mejoras
#
#===============================================================================

#TODO Hacer que no se rompa cuando las secciones estan vacias


# MODULE PLAIN API =============================================================
# TODO Media al pedo la API???
# Compile:
#   .. system: Parser.System type object to compile.
#   .. @ returns: A Compiler instance with the compiled system.
def Compile(system):
    _cmp = Compiler()
    _cmp.compile(system)
    return _cmp

#===============================================================================




# THE COMPILER =================================================================

class Compiler(object):
    """
    """

    # 
    FILEHEADER = \
    """********** F A L L U T O 2.0 COMPILED SYSTEM FOR NuSMV **********\n\n"""

    #
    __glinst = "Glob#inst"

    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)
    

    def __init__(self):
        self.compiledstring     = ""
        self.compiledproperties = []

        self.sys                = None
        self.tl                 = TabLevel()

        self.ctable             = {}    # 3 levels map: inst->var->compiledVar
        self.varset             = set([])   # all program variables set.
        self.syncdict           = {}
        self.transdict          = {}    # read method fillTransCompilingDict
        self.gtctable           = {}    # read method fillGTCTable
    #.......................................................................
    def compile(self, system):
        assert isinstance(system, Parser.System)
        self.sys = system
        # fill tables
        self.fillVarCompilationTable()
        self.fillSyncTransDict()
        self.fillTransCompilingDict()
        self.fillGTCTable()
        #        
        self.compileSystem()
    #.......................................................................
    def fillGTCTable(self):
        """ 
            Fill the transitions global compilation table. This table is used
            to compile events in propositional formulas of properties and
            contraints.
        """
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                self.gtctable[inst.name + '.' + f.name] \
                    = self.compileFaultActionVar(inst.name, f.name)
            # Normal transitions have already been compiled into self.transdict
            for t in pt.transitions:
                self.gtctable[inst.name + '.' + t.name] \
                    = self.transdict[inst.name][t.name][0]
    #.......................................................................
    def fillVarCompilationTable(self):
        # local vars
        self.ctable[Compiler.__glinst] = {}
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            self.ctable[inst.name] = {}
            for lv in pt.localvars:
                self.ctable[inst.name][lv.name] = \
                    self.compileLocalVar(inst.name, lv.name)
                # global instance for properties and contraints compilation
                self.ctable[Compiler.__glinst][inst.name + '.' + lv.name] = \
                    self.ctable[inst.name][lv.name]
                if lv.type == Types.Symbol:
                    # Symbol values
                    for x in lv.domain:
                        self.ctable[inst.name][x] = self.compileSymbValue(x)
                        # global instance again
                        self.ctable[Compiler.__glinst][x] = \
                            self.ctable[inst.name][x]

        # context vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for i in range(0,len(pt.contextvars)):
                scv = _str(pt.contextvars[i])
                siv = _str(inst.params[i])
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
                else:
                    assert isBool(siv) or isInt(siv)
                    self.ctable[inst.name][scv] = self.compileBOOLorINT(siv)
    #.......................................................................
    def compileBOOLorINT(self, value):
        return value
    #.......................................................................
    def fillSyncTransDict(self):
        stdict = {}
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            n = len(pt.contextvars)
            i = 0
            for stname in [_str(x) for x in inst.params[n::]]:
                # get the real transition:
                ptstname = _str(pt.synchroacts[i])
                for t in pt.transitions:
                    if t.name == ptstname:                        
                        try:
                            stdict[stname].append( (inst, t) )
                        except:
                            stdict[stname] = [ (inst, t) ]
                i += 1
        self.syncdict = stdict
    #.......................................................................
    def compileSystem(self):
        """
            Compiles the whole system except for the properties.
        """
        self.save(self.comment(Compiler.FILEHEADER), False, True)
        self.save("MODULE main()\n")
        self.tl.i()
        self.buildVarSection()
        self.buildInitSection()
        self.buildTransSection()
        self.tl.d()
        self.buildContraints()
        # build properties and queue them into the propertie vector
        self.buildProperties()
    #.......................................................................
    def buildProperties(self):
        for p in self.sys.properties.itervalues():
            formula = self.replaceEvents(p.formula)
            if p.type == Types.Ctlspec:
                pRepr = "CTLSPEC "+putBracketsToFormula(p.formula) 
                pComp = "CTLSPEC "+self.compileAST(Compiler.__glinst, formula)
                self.compiledproperties.append( (pRepr, pComp) )
            elif p.type == Types.Ltlspec:
                pRepr = "LTLSPEC "+putBracketsToFormula(p.formula) 
                pComp = "LTLSPEC "+self.compileAST(Compiler.__glinst, formula)
                self.compiledproperties.append( (pRepr, pComp) )
            elif p.type == Types.Nb:
                self.compiledproperties.append(self.compileNbPropertie(p))
            elif p.type == Types.Fmf or p.type == Types.Fmfs:
                self.compiledproperties.append(self.compileFmfPropertie(p))
            else:
                debugERROR("bad type for propertie: " + p.type)
    #.......................................................................
    def compileNbPropertie(self, p):
        """
        Compile a normal behaiviour propertie: 
                G V( !fault.active ) -> prop
        We want to know if 'prop' is guaranteed if we walk only over normal 
        traces where faults don't accur.
        """
        strprop = "LTLSPEC "
        faults = []
        for i in self.sys.instances.itervalues():
            pt = self.sys.proctypes[i.proctype]
            for f in pt.faults:
                faults.append(self.compileFaultActionVar(i.name, f.name))
        if faults != []:
            strprop += "( G ! (" + Compiler.__actvar + " in " \
                  + self.compileSet(faults) + " ) ) -> "
        formula = self.replaceEvents(p.formula)
        strprop += self.compileAST(Compiler.__glinst, formula)
                  
#        debugGREEN("Compiling normal behaviour propertie:\n\t" + strprop)             
        return ("NORMAL_BEAHAIVIOUR "+putBracketsToFormula(p.formula), strprop)
    #.......................................................................
    def compileFmfPropertie(self, p):
        """
        Compile a finitely many fault propertie.
        We wan't to know if a property holds in cases where finally some faults
        don't occur ever again.
        """
        strprop = "LTLSPEC "
        faults = []
        if p.type == Types.Fmfs:
            for i in self.sys.instances.itervalues():
                pt = self.sys.proctypes[i.proctype]
                for f in pt.faults:        
                    faults.append(self.compileFaultActionVar(i.name,f.name))
        elif p.type == Types.Fmf:
            for f in [_str(x) for x in p.params]:
                assert '.' in f
                ii, ff = f.split('.',1)
                faults.append(self.compileFaultActionVar(ii,ff))
        else:
            assert False
        if faults != []:
            strprop += "( F G ! (" + Compiler.__actvar + " in " \
                + self.compileSet(faults) + ") ) -> "
        formula = self.replaceEvents(p.formula)
        strprop += self.compileAST(Compiler.__glinst,formula)

#        debugGREEN("Compiling finitely many faults propertie:\n\t" + strprop)
        
        if p.type == Types.Fmfs:
            return \
            ("FINITELY_MANY_FAULTS " + putBracketsToFormula(p.formula), strprop)
        else:
            return \
            ("FINITELY_MANY_FAULT (" \
            + self.symbolSeparatedTupleString( \
            [_str(x) for x in p.params], False, False, ',') \
            + ';' + putBracketsToFormula(p.formula), strprop)
    #.......................................................................
    def buildContraints(self):
        self.save("\n\n")
        self.save(self.comment(" @@@ SYSTEM CONTRAINTS"))
        if not Types.WFDisable in \
            [x.type for x in self.sys.options.itervalues()]:
            self.buildWeakFairContraint()
        if not Types.FFDisable in \
            [x.type for x in self.sys.options.itervalues()]:
            self.buildFaultFairContraint()
        if Types.Checkdk in [x.type for x in self.sys.options.itervalues()]:
            self.buildDkCheckContraint()
        for c in self.sys.contraints.itervalues():
            self.buildNormalContraint(c)
        self.buildCTLvsLTLCompatibilityContraint()
    #.......................................................................
    def buildCTLvsLTLCompatibilityContraint(self):
        self.save("\n")
        self.save(self.comment("  @@ CTL vs LTL COMPATIBILITY CONTRAINT"))
        self.save("FAIRNESS TRUE") 
    #.......................................................................
    def buildDkCheckContraint(self):
        self.save("\n")
        self.save(self.comment("  @@ DEADLOCK CHECK CONTRAINT"))
        self.save("CTLSPEC AG " + Compiler.__actvar + " != " + Compiler.__dkact) 
    #.......................................................................
    def buildWeakFairContraint(self):
        # SYSTEM - MODULE FAIRNESS
        # Weak fairness para modulos. Un modulo que esta infinitamente 
        # habilitado para realizar alguna accion normal, debe ser atendido 
        # infinitamente a menudo. Un modulo puede entrar en deadlock cuando 
        # todas sus guardas son inhabilitadas, pero puede salir del mismo a
        # partir de cambios en el resto del sistema.
        # Pedimos fairness para las acciones del modulo o para el estado de
        # deadlock del modulo, de esta manera si el modulo nunca cae en dedalock
        # (siempre esta habilitado para realizar una accion normal) entonces en 
        # algun momento va a ser atendido.

        for inst in self.sys.instances.itervalues():
            self.save("\n")
            self.save(self.comment("  @@ MODULE FAIRNESS FOR "+inst.name+"\n"))
            actVec = []
            pt = self.sys.proctypes[inst.proctype]

            # put transition names into the list
            for t in pt.transitions:
                actVec.append(self.transdict[inst.name][t.name][0])

            #if module hasn't got any actions:
            if actVec == []:
                continue
            
            # transitions pre negations (module deadlock condition)
            dkVec = []
            for t in pt.transitions:
                pre = self.transdict[inst.name][t.name][1]
                if pre != "":
                    dkVec.append(self.neg(pre))
                           
            dkString = self.symbolSeparatedTupleString( dkVec, False, False)

            actString = Compiler.__actvar + " in " + self.compileSet(actVec)

            self.save("FAIRNESS " + (self.symbolSeparatedTupleString( \
                [dkString, actString], False, False, '|')))
    #.......................................................................
    def buildFaultFairContraint(self):
        # FAULT - SYSTEM FAIRNESS
        # Para evitar que las fallas se apoderen del sistema, nos restringimos
        # a trazas en las que siempre eventualmente ocurra alguna transicion
        # normal (no de falta). Por defecto se usa esta configuracion.
        
        self.save("\n")
        self.save(self.comment("  @@ FAULT SYSTEM FAIRNESS"))
        
        actionset = set([Compiler.__dkact])
        for i in self.sys.instances.itervalues():
            pt = self.sys.proctypes[i.proctype]
            for t in pt.transitions:
                actionset.add(self.transdict[i.name][t.name][0])
        self.save( "FAIRNESS (" + Compiler.__actvar + " in " + \
                  self.compileSet(list(actionset)) + ")")
    #.......................................................................
    def buildNormalContraint(self, c):
        self.save("\n")
        if c.type == "FAIRNESS":
            self.save(self.comment( "  @@ CONTRAINT: FAIRNESS " \
                                  + putBrackets(c.params[0])))
            param = self.replaceEvents(c.params[0])
            self.save( "FAIRNESS " \
                     + self.compileAST(Compiler.__glinst, param))
        elif c.type == "COMPASSION":
            self.save( self.comment("  @@ CONTRAINT: COMPASSION( " \
                     + putBrackets(c.params[0])\
                     + ', ' + putBrackets(c.params[1])))
            param0 = self.replaceEvents(c.params[0])
            param1 = self.replaceEvents(c.params[1])
            self.save( "COMPASSION (" \
                     + self.compileAST(Compiler.__glinst, param0) + ',' \
                     + self.compileAST(Compiler.__glinst, param1) + ")" )
        else:
            debugWARNING("Bad type for contraint <" + c.type + ">.")
    #.......................................................................
    def fillTransCompilingDict(self):
        """
            Fill in self.transdict.
            self.transdict is a 3 level dict:
            self.transdict[inst_name] \
                [uncompiled_trans_name] \
                    [(compiled_trans_name, trans_enable_condition)]
        """
        # Synchronous transitions
        self.transdict[Compiler.__glinst] = {}
        for st in self.syncdict.iteritems():
            elst = []
            for inst,trans in st[1]:
                pt = self.sys.proctypes[inst.proctype]
                # STOP faults that disable this transitions
                for f in pt.faults:
                    if f.type == Types.Stop:
                        if f.affects == [] or trans.name in f.affects:
                            elst.append(\
                                self.compileFaultActive(inst.name,f.name)\
                                + " = " + False )
                # Transition enable condition
                if trans.pre != None:
                    elst.append(self.compileAST(inst.name, trans.pre))

            tcname = self.compileSynchroAct(st[0])
            econd = self.symbolSeparatedTupleString(elst)
            assert elst != [] or econd == ""
            self.transdict[Compiler.__glinst][st[0]] = (tcname, econd)

        # Common transitions
        for inst in self.sys.instances.itervalues():
            self.transdict[inst.name] = {}
            pt = self.sys.proctypes[inst.proctype]
            for t in pt.transitions:
                elst = []
                if not t.name in [_str(x) for x in pt.synchroacts]:
                    # STOP faults that disable this transitions
                    for f in [x for x in pt.faults if x.type == Types.Stop]:
                        if f.affects == [] or \
                            t.name in [_str(x) for x in f.affects]:
                            elst.append( \
                                self.compileFaultActive(inst.name, f.name) + \
                                " = FALSE")
                    # Transition enable condition
                    if t.pre != None:
                        elst.append(self.compileAST(inst.name, t.pre))

                    tcname = self.compileAction(inst.name, t.name)
                    econd = self.symbolSeparatedTupleString(elst)
                    assert elst != [] or econd == ""
                    self.transdict[inst.name][t.name] = (tcname, econd)
                else:
                    # It's a synchro. Match to the corresponding global synchro
                    n = len(pt.contextvars)
                    i = 0
                    while t.name != _str(pt.synchroacts[i]):
                        i += 1
                    stname = _str(inst.params[n+i])
                    self.transdict[inst.name][t.name] = \
                        self.transdict[Compiler.__glinst][stname]
        #TODO usar este diccionario en la construccion de la transsection
    #.......................................................................
    def buildVarSection(self):
        self.save(self.comment( " @@@ VARIABLES DECLARATION SECTION." ))
        self.save("VAR")
        self.tl.i()
        # ACTION VARIABLE
        lst = set([]) 
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # faults
            for fault in pt.faults:
                lst.add(self.compileFaultActionVar(inst.name, fault.name))
            n = len(pt.contextvars)
            # transitions
            for act in pt.transitions:
                if not act.name in [_str(x) for x in pt.synchroacts]:
                    lst.add(self.compileAction(inst.name, act.name))
            # Synchro actions
            for act in [_str(x) for x in inst.params[n::]]:
                lst.add(self.compileSynchroAct(act))
            # BIZ effects
            for f in pt.faults:
                if f.type == Types.Byzantine:
                    lst.add(self.compileBizEffect(inst.name, f.name))
        # deadlock action
        lst.add(Compiler.__dkact)
        # save
        self.save(Compiler.__actvar + ':' + self.compileSet(lst) + ';')
        self.varset.add(Compiler.__actvar)

        # LOCAL VARIABLES
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                vname = self.ctable[inst.name][var.name]
                if var.type == Types.Bool:
                    self.save(vname + ":boolean;")
                else:
                    self.save(self.compileAST( inst.name, var.rawinput \
                                             , False) + ';')
                self.varset.add(vname)
        # fault activity variables
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                name = self.compileFaultActive(inst.name, f.name)
                self.save( name + ":boolean;")
                self.varset.add(name)
        self.tl.d()

    #.......................................................................
    def buildInitSection(self):
        self.save("\n\n")
        self.save(self.comment( " @@@ INITIALIZATION SECTION." ))
        self.save("INIT")
        self.tl.i()
        lst = []
        flst = ["TRUE"] # 'TRUE' so INIT never gets empty and NuSMV accepts it
        for inst in self.sys.instances.itervalues():
            pk = self.sys.proctypes[inst.proctype]
            # instance initialization
            lst.append(self.compileAST(inst.name, pk.init, True))
            # faults activation var initialization
            for fault in pk.faults:
                flst.append( self.compileFaultActive(inst.name,fault.name) \
                            + " = FALSE")
        lst.append(self.symbolSeparatedTupleString(flst, False, False))
        self.save(self.symbolSeparatedTupleString(lst, False, True))
        self.tl.d()

    #.......................................................................
    def buildTransSection(self):
        self.save("\n\n")
        self.save(self.comment( " @@@ TRANSITION SECTION." ))
        self.save("TRANS")
        self.tl.i()
        tlst = []
        # common transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for trans in pt.transitions:
                if not trans.name in [_str(x) for x in pt.synchroacts]:
                    tlst.append(self.buildCommonTrans(inst,pt,trans))
        # synchro transitions
        for trans in self.syncdict.iteritems():
            tlst.append(self.buildSynchroTrans(trans))
        # fault ocurrence transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                tlst.append(self.buildFaultTransition(inst,pt,f))
        # biz effects transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in [x for x in pt.faults if x.type == Types.Byzantine]:
                tlst.append(self.buildByzantineTrans(inst,pt,f))
        # dead lock transitions
        tlst.append( "\n" + str(self.tl) \
                   + self.comment("  @@ DEADLOCK TRANSITION\n") \
                   + str(self.tl) + self.buildDeadLockTrans())

        # Save transitions section
        self.save(self.symbolSeparatedTupleString(tlst, False, True, '|'))
        self.tl.d()
    #.......................................................................
    def buildCommonTrans(self, inst, pt, t):
        tlst = []
        # ACTION
        vset = set([])
        # set next action to this transition
        vset.add(Compiler.__actvar)
        tlst.append( self.compileNextRef(Compiler.__actvar) + " = " \
                    + self.compileTransitionName(inst.name,t.name))

        # PRECONDITIONS
        # STOP faults that disable this transitions
        for f in pt.faults:
            if f.type == Types.Stop:
                if f.affects == [] or t.name in [_str(x) for x in f.affects]:
                    tlst.append(self.compileFaultActive(inst.name, f.name) + \
                        " = FALSE")
        # Transition enable condition
        if t.pre != None:
            tlst.append(self.compileAST(inst.name, t.pre))

        # POSTCONDITIONS
        # Transition postcondition
        for p in t.pos:
            cref = self.compileLocalVar(inst.name, _str(p[0]))
            vset.add(cref)
            tlst.append( self.compileNextRef(cref) + ' ' + _str(p[1]) + ' ' \
                        + self.compileAST(inst.name, p[2]))
        # Variables that wont change
        assert vset.issubset(self.varset)
        uvset = self.varset - vset
        for v in uvset:
            tlst.append(self.compileNextRef(v) + ' = ' + v)
        # RETURN
        return self.symbolSeparatedTupleString(tlst, False, False)
    #.......................................................................
    def buildSynchroTrans(self, strans):
        # strans = (strans name, [(inst0,trans0)...(instn,transn)])
        stlst = []
        # ACTION
        vset = set([])
        # set next action to this transition
        vset.add(Compiler.__actvar)
        stlst.append(self.compileNextRef(Compiler.__actvar) + " = " \
                    + self.compileSynchroAct(strans[0]))

        # PRECONDITIONS
        for inst,trans in strans[1]:
            pt = self.sys.proctypes[inst.proctype]
            # STOP faults that disable this transitions
            for f in pt.faults:
                if f.type == Types.Stop:
                    if f.affects == [] or trans.name in f.affects:
                        stlst.append( self.compileFaultActive(inst.name,f.name)\
                                    + " = " + False )
            # Transition enable condition
            if trans.pre != None: #TODO pre = None se deberia traducir como TRUE
                stlst.append(self.compileAST(inst.name, trans.pre))
                
        # POSTCONDITIONS
        # Transition postcondition
        for inst,trans in strans[1]:
            for p in trans.pos:
                cref = self.compileLocalVar(inst.name, _str(p[0]))
                vset.add(cref)
                stlst.append( self.compileNextRef(cref) + ' '+ _str(p[1])+ ' ' \
                           + self.compileAST(inst.name, p[2]))
        # Variables that wont change        
        assert vset.issubset(self.varset)
        uvset = self.varset - vset
        for v in uvset:
            stlst.append(self.compileNextRef(v) + ' = ' + v)
        # RETURN
        return self.symbolSeparatedTupleString(stlst, False, False)
    #.......................................................................    
    def buildFaultTransition(self, inst, pt, f):
        ftlst = []
        # ACTION
        vset = set([])
        # set next action to this transition
        vset.add(Compiler.__actvar)
        ftlst.append(self.compileNextRef(Compiler.__actvar) + " = " \
                    + self.compileFaultActionVar(inst.name, f.name))

        # PRECONDITIONS
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
            cref = self.compileLocalVar(inst.name, _str(p[0]))
            vset.add(cref)
            ftlst.append( self.compileNextRef(cref) + ' ' + _str(p[1]) + ' ' \
                        + self.compileAST(inst.name, p[2]))
        # Variables that wont change
        assert vset.issubset(self.varset)
        uvset = self.varset - vset
        for v in uvset:
            ftlst.append(self.compileNextRef(v) + ' = ' + v)
        # RETURN
        return self.symbolSeparatedTupleString(ftlst, False, False)
    #.......................................................................
    def buildByzantineTrans(self, inst, pt, f):
        thistransvect = []
        exceptSet = set([])
        # set action to this transition
        thistransvect.append("next(" + Compiler.__actvar + ") = " +\
            self.compileBizEffect(inst.name, f.name))
        exceptSet.add(Compiler.__actvar)
        # Biz fault must be active
        thistransvect.append(self.compileFaultActive(inst.name,f.name))
        for e in f.affects:
            #con agregarlas a la lista de excepcion ya me aseguro de que no se
            #defina el proximo valor para la variable y por lo tanto NuSMV le
            #asigne un valor aleatorio dentro de su dominio. 8-)
            exceptSet.add(self.compileLocalVar(inst.name,_str(e)))
        #everithing else:
        for v in self.varset - exceptSet:
            thistransvect.append("next(" + v + ") = " + v)
        return self.symbolSeparatedTupleString(thistransvect,False,False)
    #.......................................................................
    def buildDeadLockTrans(self):
        result = []
        # set action to dead lock
        result.append( "next(" + Compiler.__actvar + ") = " + Compiler.__dkact)

        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]

            # negation of local transitions preconditions
            for trans in pt.transitions:
                if not trans.name in [_str(x) for x in pt.synchroacts]:
                    tvect = []
                    if trans.pre != None:
                        tvect.append( \
                            self.neg(self.compileAST(inst.name,trans.pre)))
                    for sf in self.getStopFaultsForAction(inst,trans):
                        tvect.append(self.compileFaultActive(inst.name,sf.name))
                    result.append(self.symbolSeparatedTupleString( \
                        tvect, False, False, '|'))

        # negation of synchro transitions preconditions
        for (sync , tlist) in self.syncdict.iteritems():
            syncvect = []
            for (inst,t) in tlist:
                syncvect.append(self.neg(self.compileAST(inst.name,t.pre)))
                for f in self.getStopFaultsForAction(inst, t):
                    syncvect.append(self.compileFaultActive(inst.name,f.name))
            result.append(self.symbolSeparatedTupleString(syncvect, \
                False, False, '|'))
        
        # nothing else changes
        for v in self.varset - set([Compiler.__actvar]):
            result.append( "next(" + v + ") = " + v)

        return self.symbolSeparatedTupleString(result, False, False)
    
    #.......................................................................
    """
        **
        ** Gets stop faults that affect action in instance
        **
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
            if (act.name in [_str(x) for x in f.affects]) or (f.affects == []) \
                and act.name != f.name:
                faultlist.append(f)
        return faultlist
    #.......................................................................
    def comment(self, string):
        """
            Returns a NuSMV comment string representing 'string'
        """
        return "--" + string
    #.......................................................................
    def neg(self, string):
        if string == None or string == "":
            return ""
        else:
            return "!(" + string + ")"
    #.......................................................................
    def save(self, string, tablevel = True, enter = True):
        """
            Saves string into the compiled system string. Adds '\n' to the end
            if enter is True. Adds self.tl to the start if tablevel is True.
        """
        if tablevel:
            self.compiledstring += str(self.tl)
            
        self.compiledstring += string
        
        if enter:
            self.compiledstring += "\n"
    #.......................................................................
    # writeSysToFile:
    #   .. filename: Name of the file to create and write.
    #   .. props: List of integers, representing the index of the compiled 
    #             properties we wan't to right ass well to the file. Value 
    #             'None' will write all the properties to the file.
    def writeSysToFile(self, filename, props = []):
        """
            Write the compiled system (and optionally the compiled properties)
            to '_file'
        """
        #open file and truncate at beginning
        fileOutput = open(filename, 'w+')                       
        fileOutput.write(self.compiledstring)
        if props != []:
            fileOutput.write("\n" + self.comment(" @@@ PROPERTIES \n"))

        if props == None:
            for p in self.compiledproperties:
                fileOutput.write(\
                    "\n" + self.comment("  @@ PROPERTIE: " + p[0] + "\n"))
                fileOutput.write(p[1] + "\n")
        else:
            for i in props:
                try:
                    p = self.compiledproperties[i]
                    fileOutput.write(\
                        "\n" + self.comment("  @@ PROPERTIE: "+ p[0] +"\n"))
                    fileOutput.write(p[1] + "\n")
                except:
                    debugWARNING( "Propertie index out of range. Not writing " \
                                + "propertie " + str(i) + " to file.\n")
    #.......................................................................
    def symbolSeparatedTupleString(self, array, parent = False, enter=False, \
                                     amp = '&'):
        parentopen = ""
        parentclose = ""
        amperson = " " + amp + " "
        if parent:
            parentopen = "("
            parentclose = ")"
        if enter:
            amperson = amperson + "\n" + str(self.tl)

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

    #.......................................................................

    # COMPILATION METHODS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #.......................................................................
    def compileLocalVar(self, iname, vname):
        return "lvar#" + iname + "#" + vname
    #.......................................................................
    def compileSymbValue(self, x):
        return "sv#" + x
    #.......................................................................
    def compileFaultActionVar(self, iname, fname):
        return "fault#" + iname + '#' + fname
    #.......................................................................
    def compileAction(self, iname, actname):
        return "trans#" + iname + "#" + actname
    #.......................................................................
    def compileSynchroAct(self, saname):
        return "synchro#" + saname
    #.......................................................................
    def compileBizEffect(self, iname, fname):
        return "bizE#" + iname + '#' + fname
    #.......................................................................
    def compileSet(self, _set):
        lst = list(_set)
        if lst == []:
            return "{}"
        string = "{ " + str(lst[0])
        for x in lst[1::]:
            string += ', ' + str(x) 
        return string + '}'
    #.......................................................................
    def replaceEvents(self, ast):
        if isinstance(ast, pyPEG.Symbol):
            ps = pyPEG.Symbol(ast.__name__,[])
            if ast.__name__ == "EVENT":
                ps.what.append(unicode('('))
                ps.what.append(unicode(Compiler.__actvar)) 
                ps.what.append(unicode(" = "))
                ps.what.append(unicode(self.gtctable[_str(ast.what[1])]))
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
            
    #.......................................................................
    def compileAST(self, iname, ast, space = True):
        sp = ""
        if space:
            sp = " "
        string = ""
        for x in _cl(ast):
            try:
                string += self.ctable[iname][x] + sp
            except:
                string += x
                if x != '!' and x != '-':
                    string += sp
        return string
    #.......................................................................
    def compileFaultActive(self, iname, fname):
        return "factive#" + iname + '#' + fname
    #.......................................................................
    def compileNextRef(self, ref):
        return "next(" + ref + ")"
    #.......................................................................
    def compileTransitionName(self, iname, tname):
        return "trans#" + iname + '#' + tname
    #.......................................................................
    #.......................................................................

    #~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


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
    
