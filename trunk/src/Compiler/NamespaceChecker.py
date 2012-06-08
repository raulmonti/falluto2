#===============================================================================
# Modulo Checker.py
# 8 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

"""
    Este modulo brinda las utilidades para comprobar la correctitud gramatical 
    del input al programa.
"""

from Exceptions.Exceptions import *
        


class NamespaceChecker():
    def __init__(self):
        self.checkingResult = True
        self.modulesNames = []
        self.instancesNames = []

    def checkAllNamespace(self, system):
        self.checkSystemNamespace(system)


    def checkRepeated(self, mlist):
        varCheckList = []
        for x in mlist:
            if x.name in varCheckList:
                raise SyntaxError(str(x.name))
            else:
                varCheckList.append(x.name)
        return varCheckList


    def checkSystemNamespace(self, system):
        # Nombre de modulo repetido?
        try:
            self.modulesNames = self.checkRepeated(system.modules)
        except SyntaxError, E:
            lines = []
            for x in system.modules:
                if x.name == str(E):
                    lines.append(str(x.line))
            raise RedeclaredError("MODULE " + str(E), lines)

        # Nombre de instancia repetida?
        try:
            self.instancesNames = self.checkRepeated(system.instances)
        except SyntaxError, E:
            lines = []
            for x in system.instances:
                if x.name == str(E):
                    lines.append(str(x.line))
            raise RedeclaredError("INSTANCE " + str(E), lines)

