# Modulo Compiler.py
# 10 de Junio del 2012
# Autor: Raul Monti

"""
    Compilador de Falluto a NuSMV (.fll -> .smv)
"""

import fileinput
from Debug import *
from Config import *


#ENUMERACION DE LAS VARIABLES "NUEVAS" DEL "PROGRAMA" NUSMV Y SU REPRESENTACION COMO STRING EN EL OUTPUT:

VARSDICT = { 'actionVar' : '@ACTION',
             'nnAction'  : 'NN',
           }

def formatModuleAct(moduleName, actName):
    return str(moduleName) + '@' + str(actName)

def formatModuleFault(moduleName, faultName):
    return str(moduleName) + '@' + str(faultName)


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
            self.level += other
            return self
        else:
            raise TypeError




class Compiler():
    def __init__(self, system, outputName):
        self.system = system
        self.stringOutput = ""
        self.fileOutput = open(outputName, 'w+')                                # a+ means append to the end of the file, w+ truncates the file at the beginning.
        self.tab = TabLevel()

    def out(self, string):
        self.stringOutput += string
        
    def compile(self):
        self.out("MODULE main()\n" + str(self.tab + 1) + "VAR\n")
        self.tab += 1
        self.compileVars()
        self.fileOutput.write(self.stringOutput);

    def compileActVar(self):
        self.out(str(self.tab) + VARSDICT['actionVar'] + " : {")
        
        if DEBUGTODO__:
            DebugTODO("Que pasa con las variables y acciones a "+ \
                  "las cuales no se les da nombres al crear las instancias?" + \
                  "Es mas, esta permitido hacer eso?")
            DebugTODO("Hay faltas sincronizadas? se agregan a los parametros "+\
                      "como se hace con las actions? Hay faltas sin nombre?")

        ls = []
        for x in self.system.instances:
            # synchronization actions:            
            module = self.system.modules[x.type]
            n = len(module.contextVars)
            for a in x.params[n::]:
                if a not in ls:
                    ls.append(a)
            
            # module actions
            count = 0
            for a in [z.name for z in module.trans]:
                if a not in [zz.name for zz in module.synchroActs]:
                    if str(a) == "":
                        a = VARSDICT['nnAction'] + str(count)
                        count += 1
                    ls.append(formatModuleAct(x.name, a))
                
            # fault ocurrence action
            for f in module.faults:
                ls.append(formatModuleFault(x.name, f.name))
        
        # add every action to the output string
        for a in ls[0:1]:
            self.out(str(a))
        for a in ls[1::]:
            self.out(", " + str(a))
        self.out("}")

    def compileVars(self):
        # actions VAR
        self.compileActVar()

