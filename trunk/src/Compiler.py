#Sab 30 de Jun 2012
#Raul Monti

from Debug import *
from Config import *
from Parser2 import Types
import Parser2
from Exceptions.Exceptions import *



#///////////////////////////////////////////////////////////////////////////////
# DEBUGING
#///////////////////////////////////////////////////////////////////////////////

debugTODO("Que pasa con las variables y acciones a "+ \
      "las cuales no se les da nombres al crear las instancias?" + \
      "Es mas, esta permitido hacer eso?")
debugTODO("Mejorar el modulo de excepciones y usarlo en todos lados")
debugTODO("Mejorar el codigo de las common transitions (usar el varSet)")
debugTODO("Ocultar todas aquellas funciones que no tengan sentido sin haber" \
        + " hecho todo el proceso de compilacion previo (cargado de tablas," \
        + " inicializaciones, etc...")


debugURGENT("Por alguna razon las transiciones de commitAtomico.fll provocan " \
    + "que el conjunto de estados inicials sea vacio y por ende la simulacion" \
    + " no sirva de nada y todas las propiedades dan true :S")

debugURGENT("-- SYSTEM MODULE FAIRNESS \\n FAIRNESS ((action# in {  })) Ocurre" \
    + " porque no hay transiciones en los modulos :S")



#///////////////////////////////////////////////////////////////////////////////
# AUXILIAR CLASSES AND FUNCTIONS
#///////////////////////////////////////////////////////////////////////////////


"""
    Para definir el nivel de tabulado a partir del cual imprimir el output.
    Para agregar un n '\t' al tabulado hacemos Tablevel += n, similarmente para 
    restar hacemos -= n. str(Tablevel) devuelve el string con la cantidad
    de \t elegidos.
"""
class TabLevel():

    def __init__(self):
        self.level = 0

    def __str__(self):
        string = ""
        for x in range(0,self.level):
            string += '\t'
        return string

    def __add__(self, other):
        if type(other) == int :
            self.level += other
            return self
        else:
            raise TypeError

    def __sub__(self, other):
        if type(other) == int :
            self.level -= other
            return self
        else:
            raise TypeError

    def reset(self):
        self.level = 0



    #.......................................................................
"""
    Algunos nombres de variables y valores para el archivo compilado .smv que 
    se pasa a NuSMV.
"""
class Names():
    actionvar = "action#"   #action variable 
    dkaction = "dk#action"  #deadlock action name (part of the actionvar domain)





#///////////////////////////////////////////////////////////////////////////////
# THE COMPILER
#///////////////////////////////////////////////////////////////////////////////
"""
    El compilador. Su metodo compile() toma los datos parseados del .fll y
    genera la traduccion a un archivo .smv para ser revisado con NuSMV.
"""
class Compiler():
    def __init__(self):
        self.sys = None
        self.stringOutput = ""
        self.fileOutput = None
        self.tab = TabLevel()
        # Tables
        self.syncdict = {}
        self.varTable = {}
        self.stopMap = {}   # module->transition/fault->[stop faults wich afect]
        #
        self.varSet = set([])



    #.......................................................................
    """ 
        Assumes that the input system is correct.
        @param system: a System() instance, with information about the input.
                Use Parser.py to fill this information.
        @param outputName: Name of the output file, although the 
                system.options.sysname has presedence over this param.
    """
    def compile(self, system, outputName = "defaultOutput.smv"):
        assert system
        self.sys = system
        self.compile_system()
        if system.options:
            if system.options.sysname != "":
                outputName = system.options.sysname
            
        # a+ means append to the end of the file, w+ truncates the file at 
        # the beginning.
        self.fileOutput = open(outputName + ".smv", 'w+')                       
        self.fileOutput.write(self.stringOutput)
        self.fileOutput.close()
        
        debugMAGENTA("Output written to " + outputName + ".smv")
        return outputName + ".smv"


    #.......................................................................
    """
        Compiles de System into self.stringOutput.
    """
    def compile_system(self):
        self.out("MODULE main()\n")
        self.fill_var_table()
        self.fill_var_set()
        self.fill_stop_map()
        self.tab += 1
        self.build_var_section()
        self.build_init_section()
        self.build_trans_section()
        self.tab -= 1
        self.out("\n\n\n")
        self.build_contraints()
        self.build_ltlspecs()


    #.......................................................................
    def fill_var_table(self):
        #local vars:
        for i in self.sys.instances.itervalues():
            m = i.module
            for v in self.sys.modules[m].localVars:
                c = self.compile_local_var(i.name, v.name)
                self.add_to_var_table(i.name, v.name, c)                    
        """#local faults:
        for i in self.sys.instances.itervalues():
            m = i.module
            for f in self.sys.modules[m].faults:
                c = self.compile_local_fault( i.name, f.name)
                self.add_to_var_table(i.name, f.name, c)
        """
        #context vars:
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for k in range(0, len(m.contextVars)):
                v = m.contextVars[k]
                c = i.params[k]
                if "." in c:
                    mm, p, vv = c.partition('.')
                    c = self.compile_local_var(mm,vv)
                self.add_to_var_table(str(i.name), str(v), str(c))


    #.......................................................................
    def fill_var_set(self):
        #local variables (from vartable)
        for i in self.varTable.itervalues():
            for (x,v) in i.iteritems():
                self.varSet.add(v)
        #faults activation vars
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:
                if f.faulttype != 'TRANSIENT':
                    self.varSet.add(self.compile_fault_active(i.name,f.name))
        #action
        self.varSet.add(Names.actionvar)




    #.......................................................................
    def fill_stop_map(self):
        for m in self.sys.modules.itervalues():
            self.stopMap[m.name] = {}
            for f in m.faults:
                self.stopMap[m.name][f.name] = []
            for t in m.trans:
                self.stopMap[m.name][t.name] = []

        for m in self.sys.modules.itervalues():
            for f in m.faults:
                if f.faulttype == 'STOP':
                    if f.efects == []:
                        #afecta a todos las transiciones de falla y la comunes
                        for t in m.trans:
                            self.stopMap[m.name][t.name].append(f.name)
                        for ff in m.faults:
                            self.stopMap[m.name][ff.name].append(f.name)
                    else:
                        #solo afecta a las que define
                        for tname in f.efects:
                            self.stopMap[m.name][tname].append(f.name)
                        



    #.......................................................................
    def build_var_section(self):
        self.out("VAR\n")
        self.tab += 1
        # action var
        out = Names.actionvar + " : "
        actlist = []
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            n = len(m.contextVars)
            #synchro actions
            for v in i.params[n::]:
                if not v in actlist:
                    actlist.append(v)
            #faults
            for f in m.faults:
                actlist.append(self.compile_local_fault(i.name, f.name))
            #local actions
            counter = 1
            for a in m.trans:                
                if not a.name in m.synchroActs:
                    c = a.name
                    if c == "":
                        c = self.compile_NN_action(i.name, counter)
                        counter += 1
                    else:
                        c = self.compile_local_act(i.name, c)
                    actlist.append(c)
            #BIZ efects action
            for f in self.sys.modules[i.module].faults:
                if f.faulttype == 'BIZ':
                    actlist.append(self.compile_biz_efect(i.name,f.name))

        #Dead Lock Action
        actlist.append(Names.dkaction)

        #output action var
        out += self.compile_set(actlist)
        self.out( out + ";" )

        # other vars
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            #fault active vars
            for f in m.faults:
                self.out( self.compile_fault_active(i.name, f.name) + \
                          " : boolean;")
            #local vars
            for v in m.localVars:
                out = self.compile_local_var(i.name, v.name) + " : "
                if v.domain.type == Types.BOOL:
                    out += "boolean;"
                elif v.domain.type == Types.SET:
                    out += self.compile_set(v.domain.domain) + ";"
                elif v.domain.type == Types.RANGE:
                    out += self.compile_range(v.domain.domain) + ";"
                else:
                    raise TypeError(v.domain.type)
                self.out(out)
        # restore tab level
        self.tab -= 1




    #.......................................................................
    def build_init_section(self):
        array = []
        array1 = []

        #init fault active vars
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:
                array.append(self.compile_fault_active(i.name, f.name) + \
                            " = FALSE")
        array1.append(self.ampersonseparatedtuplestring(array, False, False))

        
        #local inits:
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for init in m.init:
                array1.append(self.compile_prop_form(i.name, init))
        
        # Action var must be diferent of deadlock at start :| Otherwise I can't 
        # correctly check for deadlocks. Notice that the initial value of
        # actionvar does not have any meaning.
        array1.append(Names.actionvar + "!=" + Names.dkaction)

        if array1 != ['']:
            self.out("\n")
            self.out( "INIT\n" )
            self.tab += 1
            self.out(self.ampersonseparatedtuplestring(array1, False, True))
            #restore tab level
            self.tab -= 1


    #.......................................................................
    def build_trans_section(self):
        self.out("\n")
        self.out("TRANS\n")
        self.tab += 1
        transvect = []
        #local transitions
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for t in [x for x in m.trans if not x.name in m.synchroActs]:
                thistransvect = []
                #STOP faults which desable the transition:
                for f in m.faults:
                    if f.faulttype == "STOP" and (t.name in f.efects \
                        or f.efects == []):
                        thistransvect.append(self.compile_fault_active(i.name, \
                                f.name) + " = FALSE")
                #trans enabling condition
                if DEBUGSMV__:
                    thistransvect.append(" [[ PRE ]] ")
                thistransvect.append(self.compile_prop_form(i.name,t.pre.val))
                #set action next to this transition
                if DEBUGSMV__:
                    thistransvect.append(" [[ EVENT ]] ")
                thistransvect.append( "next("+Names.actionvar+") = "+ \
                        self.compile_local_act(i.name,t.name))
                #transition postcondition
                if DEBUGSMV__:
                    thistransvect.append(" [[ POS ]] ")
                for e in t.pos:
                    if isinstance(e.val, Parser2.Set) or \
                        isinstance(e.val, Parser2.Range):
                        thistransvect.append( "next(" + \
                            self.compile_local_var(i.name,e.name) + ") in " + \
                            str(self.compile_it(i.name,e.val)))
                    else:
                        thistransvect.append( "next(" + \
                            self.compile_local_var(i.name,e.name) + ") = " + \
                            str(self.compile_it(i.name,e.val)))
                #everything else must remain the same
                #instance vars
                if DEBUGSMV__:
                    thistransvect.append(" [[ OTHERS ]] ")
                posvars = [x.name for x in t.pos]
                for (ins,v) in self.varTable.iteritems():
                    mod = self.sys.modules[self.sys.instances[ins].module]
                    if ins == i.name:
                        for (x,y) in v.iteritems():
                            if not x in posvars + mod.contextVars:
                                thistransvect.append("next(" + y \
                                    + ") = " + y)                                
                    else:
                        for (x,y) in v.iteritems():
                            if not x in mod.contextVars:
                                thistransvect.append("next(" + y + ") = " + y)
                    #fault active vars
                for ins in self.sys.instances.itervalues():
                    mod = self.sys.modules[ins.module]
                    for f in mod.faults:
                        if f.faulttype != "TRANSIENT":
                            thistransvect.append("next(" \
                                + self.compile_fault_active(ins.name, f.name) \
                                + ") = " + self.compile_fault_active( \
                                ins.name, f.name))

                #append this transition to the transition vector
                transvect.append(self.ampersonseparatedtuplestring( \
                        thistransvect, False, False))

        #fault transitions
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:                
                thistransvect = []
                exceptSet = set([])
                #STOP faults which desable the transition (only total faults 
                #can stop fault transitions)
                for sf in m.faults:
                    if sf.faulttype == "STOP" and sf.efects == []:
                        thistransvect.append(self.compile_fault_active(i.name, \
                                sf.name) + " = FALSE")
                #if not transient
                if f.faulttype != 'TRANSIENT':
                    #not active now but will be active in next
                    c = self.compile_fault_active( i.name, f.name)
                    thistransvect.append( "!"+ c)
                    thistransvect.append( "next(" + c + ")")
                    exceptSet.add(c)
                #pre
                thistransvect.append( self.compile_prop_form(i.name, f.pre))
                #pos
                for e in self.compile_next_pred(i.name, f.pos):
                    thistransvect.append(e)
                for e in f.pos:
                    exceptSet.add(self.compile_local_var(i.name, e.name))
                #action
                thistransvect.append("next(" + Names.actionvar + ") = " +\
                    self.compile_local_fault(i.name, f.name))
                exceptSet.add(Names.actionvar)
                #everithing else:
                for v in self.varSet - exceptSet:
                    thistransvect.append("next(" + v + ") = " + v)

                #Only for BIZ faults
                if f.faulttype == 'BIZ':
                    transvect.append(self.build_biz_efect_trans(i.name, f))

                #append this transition to the transition vector
                transvect.append(self.ampersonseparatedtuplestring( \
                        thistransvect, False, False))
                        
                debugLBLUE("Compiling transition for fault " + f.name + " of instance " + i.name + ": " + str(transvect[-1]))
        
        #synchro transitions
        #get dict with all synchro transitions and instances related to them:
        self.syncdict = self.get_sync_act_dict()
        for (sa,il) in self.syncdict.iteritems(): # for (synchro action, instance list) in ...
            thistransvect = []
            exceptSet = set([])
            #stop faults which disable this action
            for iname in il:
                i = self.sys.instances[iname]
                m = self.sys.modules[i.module]
                for f in m.faults:
                    if f.faulttype == 'STOP' and \
                        (sa in [self.compile_action(iname,x) for x in f.efects]\
                        or f.efects == []):
                        thistransvect.append("!" + self.compile_fault_active( \
                            iname, f.name))
                                   
            #pre and pos for each instance that has this SA
            for iname in il:
                i = self.sys.instances[i.name]
                m = self.sys.modules[i.module]
                for t in m.trans:
                    if t.name == sa:
                        #pre
                        thistransvect.append( self.compile_prop_form(iname, \
                            t.pre))
                        #pos
                        for e in self.compile_next_pred(iname, t.pos):
                            thistransvect.append(e)
                        for e in t.pos:
                            exceptSet.add(self.compile_local_var(iname, e.name))
                        break

            #action
            thistransvect.append("next(" + Names.actionvar + ") = " + sa)
            exceptSet.add(Names.actionvar)

            #everithing else:
            for v in self.varSet - exceptSet:
                thistransvect.append("next(" + v + ") = " + v)
            
            #append this transition to the transition vector
            transvect.append(self.ampersonseparatedtuplestring( \
                thistransvect, False, False))

        # deadlock transition:
        transvect.append(self.ampersonseparatedtuplestring( \
            self.build_dk_trans_vect(), False, False, '&'))

        self.out(self.ampersonseparatedtuplestring(transvect, False, True, '|'))
        #restore tab level
        self.tab -= 1



    #.......................................................................
    """
        Build the transitions that represents the transition into a deadlock 
        state. 
        If no good transition can be made, then we will possibly make a 
        transition into a deadlock state. I say possible because we could also 
        make a transition into a fault state if some fault transition is 
        available.
    """
    def build_dk_trans_vect(self):
        result = []
    
        for inst in self.sys.instances.itervalues():
            mod = self.sys.modules[inst.module]

            # negation of local transitions preconditions
            for trans in mod.trans:
                if not trans.name in mod.synchroActs:
                    transvect = []
                    transvect.append(self.neg( \
                        self.compile_prop_form(inst.name, trans.pre.val)))
                    for stop in self.stopMap[mod.name][trans.name]:
                        transvect.append(self.compile_fault_active(inst.name, \
                            stop))
                    result.append(self.ampersonseparatedtuplestring( \
                    transvect, False, False, '|'))

        # negation of synchro transitions preconditions
        for (sync , insts) in self.syncdict.iteritems():
            syncvect = []
            for iname in insts:
                inst = self.sys.instances[iname]
                m = self.sys.modules[inst.module]
                for tr in m.trans:
                    if tr.name == sync:
                        syncvect.append(self.neg(
                            self.compile_prop_form(inst.name, tr.pre.val)))
                        break
            result.append(self.ampersonseparatedtuplestring(transvect, \
                 False, False, '|'))

        result.append( "next(" + Names.actionvar + ") = " + Names.dkaction)
        
        # nothing else changes
        for v in self.varSet - set([Names.actionvar]):
            result.append( "next(" + v + ") = " + v)

        return result



    """
        Returns a python dict where keys are the names of each synchronization
        action in ths system and the values are python lists of instances
        which synchronice using that key.
    """
    #.......................................................................
    def get_sync_act_dict(self):
        syncdict = {} # dict[sa] = [..] where sa is a sync action and [..] is
                      # a list of instances wich synchronice using 'sa'
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            n = len(m.contextVars)
            for sa in i.params[n::]:
                if sa in syncdict:
                    syncdict[sa].append(i.name)
                else:
                    syncdict[sa] = []
                    syncdict[sa].append(i.name)
        return syncdict



    """
        Build the transitions that represent the sporadic effects of the 
        occurrence of a bizantine fault.
    """
    #.......................................................................
    def build_biz_efect_trans( self, iname, fault):
        #mod = self.sys.modules[self.sys.instances[iname].module]
        thistransvect = []
        exceptSet = set([])
        thistransvect.append(self.compile_fault_active(iname,fault.name))
        #action
        thistransvect.append("next(" + Names.actionvar + ") = " +\
            self.compile_biz_efect(iname, fault.name))
        exceptSet.add(Names.actionvar)
        for e in fault.efects: # e is type NextVal
            #con agregarlas a la lista de excepcion ya me aseguro de que no se
            #defina el proximo valor para la variable y por lo tanto NuSMV le
            #asigne un valor aleatorio dentro de su dominio. 8-)
            exceptSet.add(self.compile_local_var(iname,e))
        #everithing else:
        for v in self.varSet - exceptSet:
            thistransvect.append("next(" + v + ") = " + v)
        return self.ampersonseparatedtuplestring(thistransvect,False,False)




    """
        Compile each LTL property in the input file, plus other properties like
        deadlock check if requeried, and output them to ths NuSMV file.
    """
    #.......................................................................
    def build_ltlspecs(self):
        self.out(self.comment("LTL EPECIFICATIONS"))
        
        for ltl in self.sys.ltlspecs:
            ltlout = "LTLSPEC "
            for item in ltl.value:
                if self.is_synchro(item):
                    ltlout += "(" + Names.actionvar + " = " + item + ")"
                elif '.' in item:
                    i, p, n = item.partition('.')
                    ins = self.sys.instances[i]
                    mod = self.sys.modules[ins.module]
                    if n in [x.name for x in mod.localVars]:
                        ltlout += self.compile_local_var(i,n)
                    else:
                        ltlout += "(" + Names.actionvar + " = " \
                            + self.compile_action(i,n) + ")"
                else:
                    ltlout += item
                ltlout += " "
            self.out(ltlout)           

        # Check for deadlock if required
        self.out(self.comment("DEADLOCK CHECK"))
        if self.sys.options.checkdeadlock:
            self.out("CTLSPEC AG " + Names.actionvar + " != " + Names.dkaction )


        #build common properties
        self.out(self.comment("COMMON PROPERTIES"))
        for p in self.sys.commonprops:
            if p.type == "NORMALBEHAIVIOUR":
                self.out(self.compile_norm_bhvr_prp(p))
            elif p.type == "FINMANYFAULT" or p.type == "FINMANYFAULTS":
                self.out(self.compile_f_many_f(p))
            else:
                raise TypeError(p.type)


    #.......................................................................
    """
        Compile a normal behaiviour propertie: 
                G V( !fault.active ) -> prop
        We want to know if 'prop' is guaranteed if we walk only over normal 
        traces where faults don't accur.
    """
    def compile_norm_bhvr_prp(self, nbp):
        strprop = "LTLSPEC "
        faults = []
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:
                faults.append(self.compile_local_fault(i.name, f.name))
        if faults != []:
            strprop += "( G ! (" + Names.actionvar + " in " \
                  + self.compile_set(faults) + " ) ) -> "
        strprop += self.compile_LTL(nbp.propertie)
                  
        debugGREEN("Compiling normal behaviour propertie:\n\t" \
             + strprop)
             
        return strprop




    #.......................................................................
    
    """
        Compile a finitely many fault propertie.
        We wan't to know if a property holds in cases where finally some faults
        don't occur ever again.
    """
    
    def compile_f_many_f(self, fmfp):
        strprop = "LTLSPEC "
        faults = []
        for f in fmfp.preconditions:
            i, p, f = f.what.partition('.')
            faults.append(self.compile_local_fault(i,f))
        
        if faults != []:
            strprop += "( F G ! (" + Names.actionvar + " in " \
                + self.compile_set(faults) + ") ) -> "

        strprop += self.compile_LTL(fmfp.propertie)

        debugGREEN("Compiling finitely many faults propertie:\n\t" \
             + strprop)
             
        return strprop





    #.......................................................................
    """
        Build contraints over the traces that will be checked.
    """
    def build_contraints(self):
        for c in self.sys.contraints:
            controut = ""
            if isinstance(c, Parser2.Fairness):
                controut = "FAIRNESS "
                controut += self.compile_LTL(c.value)
            elif isinstance(c, Parser2.Compassion):
                controut = "COMPASSION( "  \
                    + self.compile_LTL(c.pre) \
                    + ", " + self.compile_LTL(c.pos) + ")"
            else:
                raise TypeError(type(c))
            self.out(controut)

        # FAULT - SYSTEM FAIRNESS
        # Para evitar que las fallas se apoderen del sistema, nos restringimos
        # a trazas en las que siempre eventualmente ocurra alguna transicion
        # normal (no de falta). Por defecto se usa esta configuracion. Se
        # puede sin embargo desactivar seteando la variables 
        # 'self.sys.options.faultsysfairdisable' como False.
        
        self.out(self.comment("FAULT SYSTEM FAIRNESS"))
        
        if not self.sys.options.faultsysfairdisable:
            actionset = [Names.dkaction]
            for i in self.sys.instances.itervalues():
                m = self.sys.modules[i.module]
                for t in m.trans:
                    actionset.append(self.trans_real_name(i.name, t.name))
            self.out( "FAIRNESS (" + Names.actionvar + " in " + \
                      self.compile_set(actionset) + ")")

        # SYSTEM - MODULE FAIRNESS
        # Weak fairness para modulos. Un modulo que esta infinitamente 
        # habilitado para realizar alguna accion, debe ser atendido 
        # infinitamente a menudo. Un modulo puede entrar en deadlock cuando 
        # todas sus guardas son inhabilitadas, pero puede salir del mismo a
        # partir de cambios en el resto del sistema.
        # Pedimos fairness para las acciones del modulo o para el estado de
        # deadlock del modulo, de esta manera si el modulo nunca cae en dedalock
        # (siempre esta habilitado para realizar un accion) entonces en algun 
        # momento va a ser atendido.
        
        self.out(self.comment("SYSTEM MODULE FAIRNESS"))
        
        if not self.sys.options.modulewfairdisable:
            fairVec = []
            for inst in self.sys.instances.itervalues():
                mod = self.sys.modules[inst.module]
                
                # instance pre negations (module deadlock condition)
                dkVec = []
                # of faults
                for f in mod.faults:
                    fpres = self.get_pre_negation(inst, f.name)
                    dkVec.append(self.ampersonseparatedtuplestring( \
                        fpres, False, False, '|'))

                # of normal transitions
                for t in mod.trans:
                    tpres = self.get_pre_negation(inst,t.name)
                    dkVec.append(self.ampersonseparatedtuplestring( \
                        tpres, False, False, '|'))
                    
                
                # module actions set 
                actVec = []
                for f in mod.faults:
                    actVec.append(self.compile_local_fault( \
                        inst.name, f.name))
                for t in mod.trans:
                    actVec.append(self.trans_real_name( \
                        inst.name, t.name))
                
                dkString = \
                    self.ampersonseparatedtuplestring( dkVec, False, False, '&')
                actString = Names.actionvar + " in " + self.compile_set(actVec)

                fairVec.append(self.ampersonseparatedtuplestring( \
                    [dkString, actString], False, False, '|'))
            
            self.out( "FAIRNESS " + \
                self.ampersonseparatedtuplestring(fairVec, False, True, '&'))







    #@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

                      #@@ CLASS COMPILATION METHODS @@#


    #.......................................................................
    def compile_local_var(self, instName, varName):
        return instName + "#" + varName


    #.......................................................................
    def compile_local_fault(self, instName, faultName):
        return instName + "#" + faultName


    #.......................................................................
    def compile_local_act(self, instName, actName):
        return instName + "#" + actName

    #.......................................................................
    def compile_action(self, iname, actname):
        i = self.sys.instances[iname]
        m = self.sys.modules[i.module]
        n = len(m.contextVars)
        index = 0
        for elem in m.synchroActs:
            if actname == elem:
                return i.params[n+index]
            index += 1
        return self.compile_local_act(iname, actname)

    #.......................................................................
    def compile_NN_action(self, instName, counter):
        return instName + "#NNact#" + str(counter)


    #.......................................................................
    def compile_fault_active(self, instName, faultName):
        return instName + "#" + faultName + "#active"

    #.......................................................................
    def compile_prop_form(self, instName, propform):
        out = ""
        for v in propform:
            if v in self.varTable[instName]:
                v = self.varTable[instName][v]
            out += v + " "
        return out

    #.......................................................................
    def compile_set(self, lst):
        lstlen = len(lst)
        lst = list(set(lst))
        if len(lst) < lstlen:
            debugRED("Warning, cutting " + str( lstlen - len(lst)) \
                + " duplicated elements in list while compiling set" )
        ret = "{ "
        if not lst == []:
            ret += lst[0]
        for v in lst[1::]:
            ret += ", " + v
        ret += " }"
        return ret


    #.......................................................................
    def compile_range(self, lst):
        return lst[0] + ".." + lst[1]

    #.......................................................................
    def compile_math(self, iname, lst):
        return self.compile_prop_form(iname, lst)

    #.......................................................................
    def compile_next_pred(self, iname, lst):
        ret = []
        for n in lst:
            ret.append("next(" + self.compile_local_var(iname, n.name) + \
            ") = " + self.compile_it(iname, n.val))
        return ret
        
    #.......................................................................
    def compile_biz_efect(self, iname, fname):
        return "bizE#" + iname + "#" + fname

    
    #.......................................................................
    def compile_var_list(self, iname, varlist):
        return [self.var_real_value(iname, v) for v in varlist]

    #.......................................................................
    def var_real_value(self, iname, vname):
        inst = self.sys.instances[iname]
        mod = self.sys.modules[inst.module]
        for i in range(0, len(mod.contextVars)):
            if vname == mod.contextVars[i]:
                return inst.params[i]
        if vname in mod.localVars:
            return self.compile_local_var(iname,vname)
        # vname isn't a var -> should have checked before calling this function
        return vname


    #.......................................................................
    def comment(self, string):
        return "-- " + string


    #.......................................................................
    def compile_LTL(self, ltl):
        ltlout = ""
        for item in ltl:
            if self.is_synchro(item):
                ltlout += "(" + Names.actionvar + " = " + item + ")"
            elif '.' in item:
                i, p, n = item.partition('.')
                ins = self.sys.instances[i]
                mod = self.sys.modules[ins.module]
                if n in [x.name for x in mod.localVars]:
                    ltlout += self.compile_local_var(i,n)
                else:
                    ltlout += "(" + Names.actionvar + " = " \
                        + self.compile_action(i,n) + ")"
            else:
                ltlout += item
            ltlout += " "
        return ltlout





    #@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

                           #@@ OTHER METHODS @@#


    #.......................................................................
    def neg(self, prop):
        if prop != "":
            return "!(" + prop + ")"
        else:
            return prop


    #.......................................................................
    def out(self, string):
        self.stringOutput += str(self.tab) + string + "\n"




    #.......................................................................
    def add_to_var_table(self, instName, name, compiledName):
        if not instName in self.varTable:
            self.varTable[instName] = {}
        self.varTable[instName][name] = compiledName



    #.......................................................................
    def ampersonseparatedtuplestring(self, array, parent = True, enter=False, \
                                     amp = '&'):
        parentopen = ""
        parentclose = ""
        amperson = " " + amp + " "
        if parent:
            parentopen = "("
            parentclose = ")"
        if enter:
            amperson = amperson + "\n" + str(self.tab)

        marray = []
        for elem in array:
            if str(elem) != "":
                marray.append(elem)
        if marray == []:
            return ""
        else:
            string = parentopen + "(" + str(marray[0]) + ")"
            for elem in marray[1::]:
                string += amperson + "(" + str(elem) + ")"
            string += parentclose
            return string

    #.......................................................................
    def compile_it( self, iname, it):
        if isinstance(it, Parser2.Set):            
            return self.compile_set(self.compile_var_list(iname, it.domain))
        elif isinstance(it, Parser2.NextRef):
            return "next(" + it.name + ")"
        elif isinstance(it, Parser2.Math):
            return self.compile_math(iname, it.val)
        elif isinstance(it, Parser2.PropForm):
            return self.compile_prop_form(iname, it.val)
        elif isinstance(it, Parser2.Ident):
            return str(it.name)
        elif isinstance(it, Parser2.Range):
            return self.compile_range(it.domain)
        else:
            raise TypeError(it)



    #.......................................................................
    def is_synchro(self, action, instname = ""):
        if instname == "":
            for i in self.sys.instances.itervalues():
                m = self.sys.modules[i.module]
                n = len(m.contextVars)
                if action in i.params[n::]:
                    return True
        else:
            i = self.sys.instances[instname]
            m = self.sys.modules[i.module]
            n = len(m.contextVars)
            if action in i.params[n::]:
                return True
            
        return False


    #.......................................................................
    """
        Some transitions are synchronization transitions. This transitions
        dont have the name given by compile_local_trans. Thereby this function
        returns the synchronization name for those transitions and the
        one return by compile_local_trans for the others.
    """
    def trans_real_name(self, instname, transname):
        inst = self.sys.instances[instname]
        mod = self.sys.modules[inst.module]
        for n in range(0,len(mod.synchroActs)):
            if transname == mod.synchroActs[n]:
                return inst.params[len(mod.contextVars)+n]
        return self.compile_local_act(instname, transname)



    #.......................................................................
    """
        **
        ** Get a list of a transition's compiled preconditions negated.
        **
        
        @return:
            a list of transition named 'action' compiled preconditions.
        @instname:
            Instance where 'action' belongs (only useful if 'action' insn't a 
            synchronization action)
        @action:
            Name of the transition to check for preconditions
    """
    def get_pre_negation(self, inst, action):
        prelist = []
        if self.is_synchro(action, inst.name):
            # On synchronization actions, we need to check preconditions in
            # every instance that synchronises
            for i in self.sys.instances.itervalues():
                prelist += self.get_pre_negation_aux(i, action)
        else:
            prelist = self.get_pre_negation_aux(inst, action)
        
        return prelist



    #.......................................................................        
    """
        Auxiliary function for get_pre_negation.
        @return:
            List of compiled preconditions of transition named 'action' in 
            instance 'inst'.
    """
    def get_pre_negation_aux(self, inst, action):
        prelist = []
        module = self.sys.modules[inst.module]
        #if action names a transition
        for t in module.trans:
            if t.name == action:
                pre = t.pre.val
                prelist.append(self.compile_prop_form(inst.name,pre))
                break
        #if action names a fault
        for f in module.faults:
            if f.name == action:
                # not to be active is a precondition of the fault
                prelist.append(self.compile_fault_active(inst.name, action))
                pre = f.pre
                prelist.append(self.neg(self.compile_prop_form(inst.name,pre)))
                break        
        # Negation of stop faults activation variable is also part of
        # the action precondition when the fault affects the action.
        stopfaults = self.get_stop_faults_for_action(inst, action)
        for sf in stopfaults:
            prelist.append(self.neg(self.compile_fault_active( \
                inst.name, sf.name)))
                
        return prelist
                


    #.......................................................................
    """
        **
        ** Gets stop fault that affect action in instance
        **
        @instance:
            Instance class instance where to check
        @action:
            Transition name to check
        @return:
            list of stop faults that affect the transition
    """
    def get_stop_faults_for_action(self, instance, action):
        faultlist = []
        mod = self.sys.modules[instance.module]
        for f in [x for x in mod.faults if x.faulttype == 'STOP']:
            # action != f.name so global stop faults dont stop them selves
            # don't know if it's right to do so.
            if (action in f.efects) or (f.efects == []) and action != f.name:
                faultlist.append(f)
        return faultlist
        
        
        
        
        

