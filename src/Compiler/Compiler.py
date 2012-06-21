# Modulo Compiler.py
# 10 de Junio del 2012
# Autor: Raul Monti

"""
    Compilador de Falluto a NuSMV (.fll -> .smv)
"""

import fileinput
from Debug import *
from Config import *
from InputManager.Parser import Parser


if DEBUGTODO__:
    DebugTODO("Mejorar el modulo de excepciones y usarlo en todos lados\n")
    DebugTODO("Hacer mas eficiente el modulo compiler.py")
    DebugTODO("Que pasa con las variables y acciones a "+ \
          "las cuales no se les da nombres al crear las instancias?" + \
          "Es mas, esta permitido hacer eso?")
    DebugTODO("Hay faltas sincronizadas? se agregan a los parametros "+ \
              "como se hace con las actions? Hay faltas sin nombre?")
    DebugTODO("ES UN ASCO EL INGLES DE LOS COMENTARIOS DE Compiler.py\n")
    DebugTODO("Se puede hablar en LTLSPEC acerca de faltas locales a los" + \
              " modulos? En tal caso el namespace de faltas es el mismo que" + \
              " el de variables. Actualmente NO se esta soportando esto\n")
    DebugTODO("No se deberia compilar nada si no hay al menos una instancia\n.")
    DebugTODO("El metodo padre deberia definir el tab para el metodo hijo\n")
    DebugTODO("Que pasa si quiero poscondiciones de fallas mas complejas y" + \
              " no simplemente & de cambios de variables\n")

################################################################################
#ENUMERACION DE LAS VARIABLES "NUEVAS" DEL "PROGRAMA" NUSMV Y SU REPRESENTACION 
#COMO STRING EN EL OUTPUT:

VARSDICT = { 'actionVar' : 'ACTION#',
             'nnAction'  : 'NN',
           }


################################################################################

def formatModuleAct(moduleName, actName):
    return str(moduleName) + '#' + str(actName)

def formatModuleFault(moduleName, faultName):
    return str(moduleName) + '#' + str(faultName)
    
def formatModuleVar(moduleName, varName):
    return str(moduleName) + '#' + str(varName)

def formatFaultActiveVar(instanceName, faultName):
    return str(instanceName + '#' + faultName + '#active')

################################################################################

def find(f, seq):
  """Return first item in sequence where f(item) == True."""
  for item in seq:
    if f(item): 
      return item

################################################################################
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



class Compiler():
    def __init__(self, system, outputName):
        self.system = system
        self.stringOutput = ""
        self.fileOutput = open(outputName, 'w+')                                # a+ means append to the end of the file, w+ truncates the file at the beginning.
        self.tab = TabLevel()
        self.fActiveVarList = []                                                # guardo el nombre de las variables de actividad de fallas aca, para luego usarlas en la inicializacion de las mismas.
        self.compiledLocalVarsList = []
        self.instanceVarTable = {}                                              # Diccionario de diccionarios con los valores de compilacion de cada variable segun la instancia de modulo a la que pertenecen
        self.synchroActs = []                                                   # Lista con los nombres de acciones de sincronizacion

    #......................................................................
    def out(self, string):
        self.stringOutput += str(string)

    #......................................................................
    def compile(self):
        if not len(self.system.instances):
            raise SyntaxError
        self.compileVars()
        self.compileInit()
        if len(self.system.timeLogics):
            self.compileLTLSpecs()
        self.tab += 1
        self.compileTrans()
        self.tab -= 1
        self.fileOutput.write(self.stringOutput);
    #......................................................................
    """ 
        Adds a relation between an original name of variable in the input and 
        the compiled name for NuSMV. It adds it to the place of the 
        corresponding instance.
    """

    def addToIVT(self, instance, key, value):
        if not instance in self.instanceVarTable:
            self.instanceVarTable[instance] = {}
        self.instanceVarTable[instance][key] = value

    #......................................................................
    def compileActVar(self):
        self.out(str(self.tab) + VARSDICT['actionVar'] + " : {")
        ls = []
        for x in self.system.instances:
            # synchronization actions:
            module = self.system.modules[x.type]
            n = len(module.contextVars)
            for a in x.params[n::]:
                if a not in ls:
                    ls.append(a)
                    self.synchroActs.append(a)

            # module actions
            count = 0
            for a in [z.name for z in module.trans]:
                if a not in [zz.name for zz in module.synchroActs]:
                    if str(a) == "":
                        a = VARSDICT['nnAction'] + str(count)
                        count += 1
                    ls.append(formatModuleAct(x.name, a))

            # fault ocurrence action, and fault activated variable
            for f in module.faults:
                ls.append(formatModuleFault(x.name, f.name))

        # add every action to the output string
        for a in ls[0:1]:
            self.out(str(a))
        for a in ls[1::]:
            self.out(", " + str(a))
        self.out("};\n")

    #......................................................................
    def compileModVars(self):
        for x in self.system.instances:
            m = self.system.modules[x.type]
            for v in m.localVars:
                self.out(self.tab)
                fv = formatModuleVar(x.name, v.name)
                self.addToIVT(x.name, v.name, fv)
                self.out( fv + " : ")
                if v.type == "RANGE":
                    self.out(str(v.domain[0] + ".." + v.domain[1] + ";\n"))
                elif v.type == "BOOLEAN":
                    self.out("boolean;\n")
                elif v.type == "SET":
                    self.out("{")
                    for a in v.domain[0:1]:
                        self.out(str(a))
                    for a in v.domain[1::]:
                        self.out(", " + str(a))
                    self.out("};\n")
            # fault activation variables
            for f in m.faults:
                self.out(self.tab)
                sf = formatFaultActiveVar(x.name, f.name)
                self.fActiveVarList.append(sf)
                self.out(sf + " : boolean;\n")

    #......................................................................
    def compileContextVars(self):
        for i in self.system.instances:
            m = self.system.modules[i.type]
            for k in range(0, len(m.contextVars)):
                v = m.contextVars[k].name
                c = i.params[k]
                if "." in c:
                    mm, p, vv = c.partition('.')
                    c = formatModuleVar(mm,vv)
                self.addToIVT(i.name, str(v), str(c))
                if DEBUG__:
                    Debug("debugLBLUE", "Adding " + v + "  --  " + c + " to the ITV of " + i.name)

    #......................................................................
    def compileVars(self):
        self.out("MODULE main()\n\n" + str(self.tab + 1) + "VAR\n")
        self.tab += 1
        # actions VAR
        self.compileActVar()
        self.compileModVars()
        self.compileContextVars()
        self.tab -= 2

    #......................................................................
    def compileFaultInit(self):
        for f in self.fActiveVarList:
            self.out(self.tab)
            self.out("( " + f + " = FALSE ) & \n")

    #......................................................................
    def compileModInit(self):
        for inst in self.system.instances:
            mod = self.system.modules[inst.type]
            self.out(self.tab)
            for init in mod.init:
                p = Parser()
                clean = p.cleanAST(init)
                for x in clean:
                    if x in self.instanceVarTable[inst.name]:
                        x = str(self.instanceVarTable[inst.name][x])
                    self.out(x + " ");
            self.out(" & \n")

    #......................................................................
    def compileInit(self):
        self.out("\n" + str(self.tab + 1) + "INIT\n")
        self.tab += 1
        # active fault variable initialization (all False at the beginning)
        self.compileFaultInit()
        # module's particular INIT's
        self.compileModInit()
        self.out(str(self.tab) + "TRUE\n")
        self.tab -= 2

    #......................................................................
    def compileLTLSpecs(self):
        self.out("\n\n" + "LTLSPEC ")
        for ltl in self.system.timeLogics:
            p = Parser()
            cltl = p.cleanAST(ltl.spec)
            DebugRED(str(cltl))
            for x in cltl:
                # habla de una variable local?
                if '.' in x:
                    xi, p, xv = x.partition('.')
                    inst = find(lambda i: i.name == xi, self.system.instances)
                    # se trata de una variable?
                    if xv in [v.name for v in self.system.modules[inst.type].localVars]:
                        x = formatModuleVar(xi,xv)
                    # se trata de una falla
                    elif xv in [f.name for f in self.system.modules[inst.type].faults]:
                        x = "(" + VARSDICT["actionVar"] + " = " + formatModuleAct(xi,xv) + ")"
                    # se trata de una transicion?
                    elif xv in [f.name for f in self.system.modules[inst.type].trans]:
                        x = "(" + VARSDICT["actionVar"] + " = " + formatModuleAct(xi,xv) + ")"
                # habla de una accion de sincronizacion?        
                elif x in self.synchroActs:
                    x = "(" + VARSDICT["actionVar"] + " = " + x + ")"
                self.out(x + " ")

    #......................................................................
    def compileTrans(self):
        self.out(str(self.tab) + "TRANS\n")
        self.tab += 1
        self.compileFaultCausedTrans()
        self.tab -= 1

    #......................................................................
    def compileFaultCausedTrans(self):
        for inst in self.system.instances:
            mname = inst.type
            for fault in self.system.modules[mname].faults:
                self.out(self.tab)
                ff = formatFaultActiveVar(inst.name, fault.name)
                self.out("( !" + ff + " & ")
                self.out(self.compileFaultPre(fault.pre) + " & ")
                self.out("next("+VARSDICT["actionVar"]+") = "+fault.name+" & ")
                self.out("next(" + ff + ") = TRUE & ")
                
                excList = [ ff, VARSDICT["actionVar"]]
                parser = Parser()
                for (x,y) in fault.pos:
                    nx = parser.cleanAST(x)
                    nx = self.instanceVarTable[inst.name][nx[0]]
                    excList.append(nx)
                    self.out( "next(" + nx + ") = (") 
                    ny = parser.cleanAST(y)
                    for string in ny:
                        if string in self.instanceVarTable[inst.name]:
                            string = self.instanceVarTable[inst.name][string]
                        self.out(string)
                    self.out(") & >>>> ")

                DebugRED(str(parser.cleanAST(fault.pre)))
                DebugRED(str(parser.cleanAST(fault.pos)))

                # vars that wont change                
                self.out(self.notChangingVarsList(excList) + ") |\n")

    #......................................................................
    def notChangingVarsList(self, exceptions = []):
        string = ""
        for v in self.fActiveVarList:
            if not v in exceptions:
                string += "next(" + v + ") = " + v + " & "
        for d in self.instanceVarTable.itervalues():
            for v in d.itervalues():
                if not v in exceptions:
                    string += "next(" + v + ") = " + v + " & "
        return string


    def compileFaultPre(self, pre):
        return " PRE "

