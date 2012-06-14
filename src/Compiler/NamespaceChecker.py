#===============================================================================
# Modulo Checker.py
# 8 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

"""
    Este modulo brinda las utilidades para comprobar la correctitud gramatical 
    del input del programa.
"""

from Exceptions.Exceptions import *
        

class NamespaceChecker():
    def __init__(self, system):
        self.system = system
        self.modulesNames = []
        self.instancesNames = []
        self.globalVarsNameTable = []
        self.fillTables()
        
    def fillTables(self):
        # Fill globalVarsNameTable
        for x in self.system.instances:
            m = self.system.modules[x.type]
            for v in m.localVars:
                self.globalVarsNameTable.append(x.name + '.' + v.name)

    def checkAllNamespace(self):
        self.checkSystemNamespace()


    def checkRepeated(self, mlist):
        varCheckList = []
        for x in mlist:
            if x.name in varCheckList:
                raise SyntaxError(str(x.name))
            else:
                varCheckList.append(x.name)
        return varCheckList


    def checkSystemNamespace(self):
        # Nombre de modulo repetido?
        try:
            self.modulesNames = self.checkRepeated(self.system.modules.itervalues())
        except SyntaxError, E:
            lines = []
            for n, x in self.system.modules:
                if x.name == str(E):
                    lines.append(str(x.line))
            raise RedeclaredError("MODULE " + str(E), lines)

        
        # Nombre de instancia repetida?
        try:
            self.instancesNames = self.checkRepeated(self.system.instances)
        except SyntaxError, E:
            lines = []
            for x in self.system.instances:
                if x.name == str(E):
                    lines.append(str(x.line))
            raise RedeclaredError("INSTANCE " + str(E), lines)
"""
    def checkInstances(self):
        for i in self.system.instances:
            for v in i.params:
                if not v in self.
"""
