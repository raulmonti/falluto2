#Sab 30 de Jun 2012
#Raul Monti

from Debug import *
from Config import *
from Parser2 import Types

#///////////////////////////////////////////////////////////////////////////////
# DEBUGING
#///////////////////////////////////////////////////////////////////////////////


if DEBUGTODO__:
    DebugTODO("No se deberia compilar nada si no hay al menos una instancia.")
    DebugTODO("Que pasa si quiero poscondiciones de fallas mas complejas y" + \
              " no simplemente & de cambios de variables")
    DebugTODO("Que pasa con las variables y acciones a "+ \
          "las cuales no se les da nombres al crear las instancias?" + \
          "Es mas, esta permitido hacer eso?")
    DebugTODO("Hay faltas sincronizadas? se agregan a los parametros "+ \
              "como se hace con las actions? Hay faltas sin nombre?")
    DebugTODO("Mejorar el modulo de excepciones y usarlo en todos lados")
    DebugTODO("Encabezar el output.fll con la fecha y algun comentario")
    DebugTODO("Cuidado: se deja poner cualquier string como palabra de" + \
              " sincronizacion en la instansiacion")




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
    

    #.......................................................................
    """ Assumes that the input system is correct. """
    def compile(self, system, outputName = "defaultOutput.smv"):
        assert system 
        self.sys = system
        self.compile_system()
        self.fileOutput = open(outputName, 'w+')                                # a+ means append to the end of the file, w+ truncates the file at the beginning.
        self.fileOutput.write(self.stringOutput)


    #.......................................................................
    def out(self, string):
        self.stringOutput += str(self.tab) + string + "\n"


    #.......................................................................
    def compile_system(self):
        self.out("MODULE main()\n")
        self.fill_var_table()
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
                if not i.name in self.varTable:
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
    def add_to_var_table(self, instName, name, compiledName):
        if not instName in self.varTable:
            self.varTable[instName] = {}
        self.varTable[instName][name] = compiledName


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
        #output everything
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
        self.out( "INIT\n" )
        self.tab += 1
        #init fault active vars
        out = "TRUE"
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for f in m.faults:
                ff = self.compile_fault_active(i.name, f.name) + " = FALSE"
                out += " & " + ff
        self.out(out)
        #local inits:
        for i in self.sys.instances.itervalues():
            m = self.sys.modules[i.module]
            for init in m.init:
                out = "& " + self.compile_prop_form(i.name, init)
                self.out(out)
        #actvar inicia como quiera :|
        #restor tab level
        self.tab -= 1


    #.......................................................................
    def build_trans_section(self):
        self.out("TRANS\n")
        self.tab += 1
        #local transitions
        
#
#
#
#   REPENSAR ESTO DE ACA ABAJO
#
#
        for i in self.sys.instances.itervalues():
            m =  self.sys.modules[i.module]
            out = "TRUE\n"
            for t in m.trans:
                # if it's a local transition
                if not t.name in m.synchroActs:
                    if t.pre.val != []:
                        out += " & " + self.compile_prop_form(i.name, t.pre.val)
                    out += " & next(" + Names.actionvar + ")=" + \
                        self.compile_local_act(i.name, t.name)
                self.out(out)
                out = ""
        #fault transitions
        
        #synchro transitions























