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
        self.varSet = None

    #.......................................................................
    """ Assumes that the input system is correct. """
    def compile(self, system, outputName = "defaultOutput.smv"):
        assert system 
        self.sys = system
        self.compile_system()
        self.fileOutput = open(outputName, 'w+')                                # a+ means append to the end of the file, w+ truncates the file at the beginning.
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
        pass

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
        array1.append(self.ampersonseparatedtuplestring(array, False))
        
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
                    if f.faulttype == "STOP" and t.name in f.efects:
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
                        str(self.compileit(i.name,e.val)))
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
                debugRED("ACA QUEDE")
                pass
                
            #STOP faults
            #TRANSIENT faults
            #BIZ faults
        
        #synchro transitions


        self.out(self.ampersonseparatedtuplestring(transvect, False, True, '|'))







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
    def compileit( self, iname, it):
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













