# Modulo de Testing para Compiler.py
# 10 de Junio del 2012
# Autor: Raul Monti

import sys, os

sys.path.append(os.path.abspath('../../'))

from Compiler.Compiler import *

if __name__ == '__main__':
    comp = Compiler([],"output.smv")
