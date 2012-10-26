#===============================================================================
# Module: Compiler.py
# Author: Raul Monti
# F A LL U T O 2.0
#===============================================================================
#
from Parser import *
import Parser
from Debug import *
import Debug
from Types import *
import Types
from Utils import *
from Utils import _cl, _str
import Utils
#
#===============================================================================

# MODULE PLAIN API =============================================================

# Compile:
#   .. system: Parser.System type object to compile
def Compile(system):
    pass
    
# Verify:
#   .. compileSys:
#   .. i:
def Verify(compiledSys, i):
    pass
#===============================================================================


# THE COMPILER =================================================================

class Compiler(object):
    """
    """

    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)

    def __init__(self):
        pass

    #.......................................................................
    def compile(self, system):
        pass
    #.......................................................................
