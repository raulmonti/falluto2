#Sab 30 de Jun 2012
#Raul Monti

from Debug import *
from Config import *
from Parser2 import Types
import Parser2

#///////////////////////////////////////////////////////////////////////////////
# DEBUGING
#///////////////////////////////////////////////////////////////////////////////


if DEBUGTODO__:
    debugTODO("No se deberia compilar nada si no hay al menos una instancia.")
    debugTODO("Que pasa si quiero poscondiciones de fallas mas complejas y" + \
              " no simplemente & de cambios de variables")
    debugTODO("Que pasa con las variables y acciones a "+ \
          "las cuales no se les da nombres al crear las instancias?" + \
          "Es mas, esta permitido hacer eso?")
    debugTODO("Hay faltas sincronizadas? se agregan a los parametros "+ \
              "como se hace con las actions? Hay faltas sin nombre?")
    debugTODO("Mejorar el modulo de excepciones y usarlo en todos lados")
    debugTODO("Encabezar el output.fll con la fecha y algun comentario")
    debugTODO("Cuidado: se deja poner cualquier string como palabra de" + \
              " sincronizacion en la instansiacion")
    debugTODO("Quitar el fault active de las fallas que son transient")
    debugTODO("Mejorar el codigo de las common transitions (usar el varSet)")
    debugTODO("Averiguar si es mas eficiente compilar local vars o buscarlas" \
            + " en la varTable\n")
    debugTODO("Cambiar '= FALSE' por '!' en los predicados ya compilados\n")



#///////////////////////////////////////////////////////////////////////////////
# AUXILIAR CLASSES AND FUNCTIONS
#///////////////////////////////////////////////////////////////////////////////


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

class Names():
    actionvar = "action#"


#///////////////////////////////////////////////////////////////////////////////
# THE COMPILER
#///////////////////////////////////////////////////////////////////////////////

"""
NAMESPACES:

    MODULE NS: module names

    LOCAL VAR NS: local vars names, fault names, context vars names, 
                  local action names

    SYNCHRO ACT NS: synchro acts names

    INSTANCES NS: instances names
    
"""



class Compiler():
    def __init__(self):
        self.sys = None
        self.stringOutput = ""
        self.fileOutput = None
        self.tab = TabLevel()
        # Tables
        self.synchroActs = []
        self.varTable = {}
        #
        self.varSet = set([])

    #.......................................................................
    """ Assumes that the input system is correct. """
    def compile(self, system, outputName = "defaultOutput.smv"):
        assert system
        self.sys = system
        self.compile_system()
        if system.name != "":
            outputName = system.name
        self.fileOutput = open(outputName + ".fll", 'w+')                       # a+ means append to the end of the file, w+ truncates the file at the beginning.
        self.fileOutput.write(self.stringOutput)



    #.......................................................................
    def compile_system(self):
        self.out("MODULE main()\n")
        self.fill_var_table()
        self.fill_var_set()
        self.tab += 1
        self.build_var_section()
        self.build_init_section()
        self.build_trans_section()
        self.tab -= 1


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
        #faults
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:
                if f.faulttype != 'TRANSIENT':
                    self.varSet.add(self.compile_fault_active(i.name,f.name))
        #action
        self.varSet.add(Names.actionvar)

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
        self.out("\n")
        self.out( "INIT\n" )
        self.tab += 1
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
        self.out(self.ampersonseparatedtuplestring(array1, False, True))
        #actvar inicia como quiera :|
        #restor tab level
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
                if DEBUG__:
                    thistransvect.append(" [[ PRE ]] ")
                thistransvect.append(self.compile_prop_form(i.name,t.pre.val))
                #set action next to this transition
                if DEBUG__:
                    thistransvect.append(" [[ EVENT ]] ")
                thistransvect.append( "next("+Names.actionvar+") = "+ \
                        self.compile_local_act(i.name,t.name))
                #trans poscondition
                if DEBUG__:
                    thistransvect.append(" [[ POS ]] ")
                for e in t.pos:
                    thistransvect.append( "next(" + \
                        self.compile_local_var(i.name,e.name) + ") = " + \
                        str(self.compile_it(i.name,e.val)))
                #everithing else must remain the same
                    #instance vars
                if DEBUG__:
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
                #in this case)
                for f in m.faults:
                    if f.faulttype == "STOP" and f.efects == []:
                        thistransvect.append(self.compile_fault_active(i.name, \
                                f.name) + " = FALSE")
                #if not transient
                if f.faulttype != 'TARNSIENT':
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
        
        #synchro transitions
        #get dict with all synchro transitions and instances related to them:
        syncdict = self.get_sync_act_dict()
        for (sa,il) in syncdict.iteritems(): # for (synchro action, instance list) in ...
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

        #TOTAL STOPS


        self.out(self.ampersonseparatedtuplestring(transvect, False, True, '|'))


    #.......................................................................
    def get_sync_act_dict(self):
        syncdict = {} # dict[sa] = [..] where sa is a sync action and [..] is
                      # a list of instances wich synchronice using sa
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
    def compile_biz_efect(seld, iname, fname):
        return "bizE#" + iname + "#" + fname






    #@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

                           #@@ OTHER METHODS @@#



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
            return self.compile_set(iname, it.domain)
        elif isinstance(it, Parser2.NextRef):
            return "next(" + it.name + ")"
        elif isinstance(it, Parser2.Math):
            return self.compile_math(iname, it.val)
        elif isinstance(it, Parser2.PropForm):
            return self.compile_prop_form(iname, it.val)
        elif isinstance(it, Parser2.Ident):
            return str(it.name)
        else:
            raise TypeError(it)













