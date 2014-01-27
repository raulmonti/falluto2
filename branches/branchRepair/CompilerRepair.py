#===============================================================================
# Module: Compiler.py
# Author: Raul Monti
# F A LL U T O 2.0
# Mon 27 Jan 2014 05:55:42 PM ART
#===============================================================================
#
from ParserRepair import *
import ParserRepair
from DebugRepair import *
import DebugRepair
from TypesRepair import *
import TypesRepair
from Utils import *
from Utils import _cl, _str
import Utils
from CheckerRepair import *
import CheckerRepair
import Mejoras

#
#===============================================================================

# TODO problema con ! var in {,,,}




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

    #
    FILEHEADER = \
    """********** F A L L U T O 2.0 COMPILED SYSTEM FOR NuSMV **********\n\n"""

    #
    __glinst = "Glob#inst"

    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)

    # to export
    _actvar = __actvar
    _dkact  = __dkact

    #.......................................................................
    def __init__(self):
        self.compiledstring     = "" # String with the compiled system
        self.compiledproperties = [] # Read buildProperties() method

        self.sys                = None
        self.tl                 = TabLevel()

        self.ctable             = {}    # 3 levels map: inst->var->compiledVar
        self.varset             = set([])   # all program variables set.
        self.syncToTrans        = {}    # read method fillSyncTransDict()
        self.gtctable           = {}    # read method fillGTCTable
        self.transdict          = {}    # read method fillTransCompilingDict
        self.synchroMap         = {}    # read method fillTransCompilingDict
        self.synchrodict        = {}    # read method fillTransCompilingDict

    #.......................................................................
    def compile(self, system):
        assert isinstance(system, Parser.System)
        self.sys = system

        # fill tables
        self.fillSyncTransDict()
        self.fillVarSet()
        self.fillVarCompilationTable()
        self.fillTransCompilingDict()
        self.fillGTCTable()

        # compile the system and save it in self.compiledstring
        self.compileSystem()


    #.......................................................................
    # Llenar un 'set' con todas los nombres de variables del programa compilado
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
                if not var.isarray:
                    self.varset.add(self.compileLocalVar(inst.name, var.name))
                else:
                    for v in self.arrayToVars(var):
                        self.varset.add(self.compileLocalVar(inst.name, v))

            # instance program counters
            self.varset.add(self.compileIPC(inst.name))


    #.......................................................................
    def arrayToVars(self, array):
        """
            Get an array type VarDeclaration and return a list with variable
            names representing each position of the array.
        """
        assert isinstance(array, Parser.VarDeclaration)
        assert array.isarray
        result = []
        f = int(array.range[0])
        t = int(array.range[1])
        for i in range(f,t+1):
            result.append(array.name + "[" + str(i) + "]")
        return result

    #.......................................................................
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
                # TODO quizas no deberia permitir esto
                else:
                    assert isBool(siv) or isInt(siv)
                    self.ctable[inst.name][scv] = self.compileBOOLorINT(siv)

        # DEFINEs
        for d in self.sys.defines.itervalues():
            dname = _str(d.dname)
            compd = self.compileDefine(dname)
            self.ctable[Compiler.__glinst][dname] = compd

            for inst in self.sys.instances.itervalues():
                iname = inst.name
                try:
                    aux = self.ctable[iname][dname]
                except:
                    self.ctable[iname][dname] = compd



    #.......................................................................
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
            for sname in [_str(x) for x in inst.params[n::]]:
                try:
                    table = self.syncToTrans[sname]
                except:
                    self.syncToTrans[sname] = {}

                # get synchronized action name from the proctype
                ptstname = _str(pt.synchroacts[i])
                for t in pt.transitions:
                    if t.name == ptstname:
                        try:
                            self.syncToTrans[sname][inst.name].append(t)
                        except:
                            self.syncToTrans[sname][inst.name] = [t]
                i += 1



# TODO termine de revisar hasta aca, y aparentemente esta todo en orden

    #.......................................................................
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
                    tcname = self.compileAction(iname, t.name)
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



    #.......................................................................
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


    #.......................................................................
    def getPreList(self, iname, trans):
        inst = self.sys.instances[iname]
        pt = self.sys.proctypes[inst.proctype]
        elst = []

        # STOP faults that disable this transitions
        for f in [x for x in pt.faults if x.type == Types.Stop]:
            if f.affects == [] or \
                trans.name in [_str(x) for x in f.affects]:
                elst.append(self.neg(
                    self.compileFaultActive(inst.name, f.name)))
        # Transition enable condition
        assert trans.pre != None
        elst.append(self.compileAST(inst.name, trans.pre))
        
        return elst
        

    #.......................................................................
    def getPosList(self, iname, trans):
        plst = []
        changed = set([])
        # Transition postcondition
        for p in trans.pos:
            cref = self.compileLocalVar(iname, _str(p[0],False))
            changed.add(cref)
            plst.append( self.compileNextRef(cref) \
                         + ' ' + _str(p[1]) + ' ' \
                         + self.compileAST(iname, p[2]))
        # program counter
        plst.append(self.compileNextRef(self.compileIPC(iname)) + ' = ' \
            + str(trans.pc))
        changed.add(self.compileIPC(iname))
        # Variables that wont change
        assert changed.issubset(self.varset)
        return plst, changed
    
        
    #.......................................................................
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
                if not t.name in [_str(x) for x in pt.synchroacts]:
                    self.gtctable[inst.name + '.' + t.name] \
                        = self.compileAction(inst.name, t.name)

        # Normal synchronous transitions
        for stname in self.syncToTrans.iterkeys():
            self.gtctable[stname] = self.compileSynchroAct(stname)

    #.......................................................................
    def compileSystem(self):
        """
            Compiles the whole system except for the properties.
        """
        self.save(self.comment(Compiler.FILEHEADER), False, True)
        self.save("MODULE main()\n")
        self.tl.i()
        self.buildDefines()
        self.buildVarSection()
        self.buildInitSection()
        self.buildTransSection()
        self.tl.d()
        self.buildContraints()
        # build properties and queue them into the propertie vector
        self.buildProperties()


    #.......................................................................
    def buildDefines(self):
        self.save(self.comment( " @@@ DEFINITIONS." ))
        for d in self.sys.defines.itervalues():
            cdname = self.compileDefine(_str(d.dname))
            self.save( "DEFINE " + cdname + " := " \
                     + self.compileAST(Compiler.__glinst, d.dvalue) + ";")


    #.......................................................................
    def buildVarSection(self):
        self.save("\n\n")
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
            # transitions
            for act in pt.transitions:
                if not act.name in [_str(x) for x in pt.synchroacts]:
                    lst.add(self.compileAction(inst.name, act.name))
            n = len(pt.contextvars)
            # Synchro actions
            for act in [_str(x) for x in inst.params[n::]]:
                lst.add(self.compileSynchroAct(act))
            # BYZ effects
            for f in pt.faults:
                if f.type == Types.Byzantine:
                    lst.add(self.compileByzEffect(inst.name, f.name))
        # deadlock action
        lst.add(Compiler.__dkact)
        # save
        self.save(Compiler.__actvar + ':' + self.compileSet(lst) + ';')

        # LOCAL VARIABLES
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                vname = self.ctable[inst.name][var.name]
                if var.type == Types.Bool:
                    #TODO muy choto este parche, corregir cuando haya tiempo
                    if var.isarray:
                        self.save( vname + " : array " + str(var.range[0]) \
                                 + ".." + str(var.range[1]) + " of boolean;")
                    else:
                        self.save(vname + ":boolean;")
                else:
                    self.save(self.compileAST( inst.name, var.rawinput \
                                             , True, pb = False) + ';')

        # FAULT ACTIVITY VARIABLES
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in [x for x in pt.faults if x.type != Types.Transient]:
                name = self.compileFaultActive(inst.name, f.name)
                self.save( name + ":boolean;")

        # INSTANC PROGRAM COUNTERs
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            self.save(self.compileIPC(inst.name) \
                + " : 0.." + str(max(len(pt.transitions)-1,0)) + ";")

        self.tl.d()


    #.......................................................................
    def buildProperties(self):
    
        if Types.Checkdk in [x.type for x in self.sys.options.itervalues()]:
            self.buildDkCheckPropertie()
    
        for p in self.sys.properties.itervalues():
            formula = self.replaceEvents(p.formula)
            if p.type == Types.Ctlspec:
                pRepr = "CTLSPEC "+putBracketsToFormula(p.formula,False) 
                pComp = "CTLSPEC "+self.compileAST(Compiler.__glinst, formula)
                self.compiledproperties.append( (pRepr, pComp) )
            elif p.type == Types.Ltlspec:
                pRepr = "LTLSPEC "+putBracketsToFormula(p.formula,False) 
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
        if p.formula.__name__ == "CTLEXP":
            strprop = "CTLSPEC"
        elif p.formula.__name__ == "LTLEXP":
            strprop = "LTLSPEC "
        else:
            assert False
        faults = []
        for i in self.sys.instances.itervalues():
            pt = self.sys.proctypes[i.proctype]
            for f in pt.faults:
                faults.append(self.compileFaultActionVar(i.name, f.name))
        if faults != []:
            if p.formula.__name__ == "CTLEXP":
                strprop += "( AG ! (" + Compiler.__actvar + " in " \
                      + self.compileSet(faults) + " ) ) -> "
            else: # p.formula.__name__ = "LTLEXP"
                strprop += "( G ! (" + Compiler.__actvar + " in " \
                      + self.compileSet(faults) + " ) ) -> "
        formula = self.replaceEvents(p.formula)
        strprop += self.compileAST(Compiler.__glinst, formula)
        return ("NORMAL_BEAHAIVIOUR "+putBracketsToFormula(p.formula,False), strprop)
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
     
        if p.type == Types.Fmfs:
            return \
            ("FINITELY_MANY_FAULTS " + putBracketsToFormula(p.formula,False), strprop)
        else:
            return \
            ("FINITELY_MANY_FAULT (" \
            + self.symbolSeparatedTupleString( \
            [_str(x) for x in p.params], False, False, ',') \
            + ';' + putBracketsToFormula(p.formula,False) + ")", strprop)
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
        for c in self.sys.contraints.itervalues():
            self.buildNormalContraint(c)
        #self.buildCTLvsLTLCompatibilityContraint()
    #.......................................................................
    def buildCTLvsLTLCompatibilityContraint(self):
        # @ deprecated ( we hace deadlock transition )
        self.save("\n")
        self.save(self.comment("  @@ CTL vs LTL COMPATIBILITY CONTRAINT"))
        self.save("FAIRNESS TRUE") 
    #.......................................................................
    def buildDkCheckPropertie(self):
        self.compiledproperties.append(("NEVER FALLS IN DEADLOCK", \
            "CTLSPEC AX AG " + Compiler.__actvar + " != " + Compiler.__dkact))


# TODO revisar que pasa con la sincronizacion cuando no se usa la variable de 
# sincronizacion en el proctype mas alla de tenerla como parametro.
    #.......................................................................
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
            self.save("\n")
            self.save(self.comment("  @@ MODULE FAIRNESS FOR "+inst.name+"\n"))
            actVec = []
            dkVec = []
            pt = self.sys.proctypes[inst.proctype]

            # not synchro transition
            slst = [_str(x) for x in pt.synchroacts]
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
                stname = _str(stname)
                sa = _str(pt.synchroacts[i])                
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

            self.save("FAIRNESS " + (self.symbolSeparatedTupleString( \
                [dkString, actString], False, False, '|')))



    #.......................................................................
    def getPreNegation(self, prelst):
        prevec = []
        for p in prelst:
            prevec.append(self.neg(p))
        return self.symbolSeparatedTupleString(prevec, False, False, amp = '|')
    


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
                if t.name not in [_str(x) for x in pt.synchroacts]:
                    actionset.add(self.transdict[i.name][t.name][t.pc][0])

        for e in self.syncToTrans.iterkeys():
            actionset.add(self.compileSynchroAct(e))

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
            for fault in [x for x in pk.faults if x.type != Types.Transient]:
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
        for trans in self.syncToTrans.iterkeys():
            tlst.append(self.buildSynchroTrans(trans))
        # fault ocurrence transitions
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                tlst.append(self.buildFaultTransition(inst,pt,f))
        # byz effects transitions
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
    
        tcname, pre, pos = self.transdict[inst.name][t.name][t.pc]
    
        tlst = []
        # set next action to this transition
        tlst.append( self.compileNextRef(Compiler.__actvar) + " = " + tcname)

        # pre and pos conditions
        tlst += pre + pos

        return self.symbolSeparatedTupleString(tlst, False, False)


    #.......................................................................
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
            cref = self.compileLocalVar(inst.name, _str(p[0],False))
            vset.add(cref)
            ftlst.append( self.compileNextRef(cref) + ' ' + _str(p[1]) + ' ' \
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



    #.......................................................................
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
            exceptSet.add(self.compileLocalVar(inst.name,_str(e)))
        #everithing else:
        for v in self.varset - exceptSet:
            thistransvect.append("next(" + v + ") = " + v)
        return self.symbolSeparatedTupleString(thistransvect,False,False)


    #.......................................................................
    def buildDeadLockTrans(self):
        # TODO usar el mapa con precondiciones de las trans para esta transicion
        result = []
        # set action to dead lock
        result.append( "next(" + Compiler.__actvar + ") = " + Compiler.__dkact)

        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # negation of local transitions preconditions
            for trans in pt.transitions:
                if trans.name not in [_str(x) for x in pt.synchroacts]:
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
        
    # TODO las dos de abajo hacen lo mismo :S
    #.......................................................................
    def compileAction(self, iname, actname):
        return "trans#" + iname + "#" + actname
    #.......................................................................
    def compileTransitionName(self, iname, tname):
        return "trans#" + iname + '#' + tname
    #.......................................................................
    def compileSynchroAct(self, saname):
        return "synchro#" + saname
    #.......................................................................
    def compileByzEffect(self, iname, fname):
        return "byzE#" + iname + '#' + fname
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
    def compileAST(self, iname, ast, space = True, pb = True):
        if ast == None:
            return ""
        if pb:
            ast = putBracketsAsList(ast)
        sp = ""
        if space:
            sp = " "
        string = ""
        for x in _cl(ast):
            try:
                string += self.ctable[iname][x] + sp
            except:
                # TODO feo parche :s
                if x == '%':
                    string += "mod"
                else:
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
    def compileBOOLorINT(self, value):
        return _str(value)
    #.......................................................................
    def compileDefine(self, name):
        return "def#" + str(name)
    #.......................................................................
    def compileIPC(self, iname):
        return "ipc#" + iname
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
    
