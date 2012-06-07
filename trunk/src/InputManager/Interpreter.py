#===============================================================================
# Modulo Intepreter.py
# 7 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

"""
    Modulo encargado de brindar una clase que permita interpretar y comprobar 
    la correctitud sintactica del input de falluto.
    Como herramienta para estos fines se usa la libreria PyPEG.
"""

from pyPEG.pyPEG import parse
from GrammarRules import SYSTEM, COMMENT
import re, fileinput

#///////////////////////////////////////////////////////////////////////////////
#   Clase dedicada a ser un interprete de archivos .fll
#   Su metodo interpret() toma un archivo, y 
#   retorna una la lista pyAST (del modulo pyPEG) con los datos interpretados, 
#   de ser correcto el input. De lo contrario devuelve None, y levanta una 
#   excepcion.

class Interpreter():

    def __init__(self):
        self.interpreted = None
        self.success = True

    def interpret(self, files):
        self.success = True
        try:
            self.interpreted = parse(SYSTEM(), files, True, COMMENT)
        except SyntaxError, E:
            self.success = False
            print "\n __3rr0r__ MODULE interpreter.py message:", E.msg, "\n"
            raise SyntaxError(E)
            return None
        return self.interpreted

#///////////////////////////////////////////////////////////////////////////////

