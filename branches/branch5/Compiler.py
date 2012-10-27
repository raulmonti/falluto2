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
# TODO Media al pedo la API???
# Compile:
#   .. system: Parser.System type object to compile.
#   .. @ returns: A Compiler instance with the compiled system.
def Compile(system):
    pass
    
#===============================================================================




# THE COMPILER =================================================================

class Compiler(object):
    """
    """

    # 
    FILEHEADER = \
    """********** F A L L U T O 2.0 COMPILED SYSTEM FOR NuSMV **********\n\n"""

    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)

    def __init__(self):
        self.compiledString     = ""
        self.compiledProperties = []

        self.sys                = None
        self.tl                 = TabLevel()

        self.ctable             = {}    # 3 levels map: inst->var->compiledVar
        self.varSet             = set([])   # all program variables set.
    #.......................................................................
    def compile(self, system):
        assert isinstance(system, Parser.System)
        self.sys = system
        self.fillVarCompilationTable()
        self.compileSystem
    #.......................................................................
    # VerifyPropertie:
    #   .. i: propertie index
    def VerifyPropertie(self, i):
        pass
    #.......................................................................
    def fillVarCompilationTable(self):
        # local vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            self.ctable[inst.name] = {}
            for lv in pt.localvars:
                self.ctble[inst.name][lv.name] = \
                    self.compileLocalVar(inst.name, lv.name)
        
        # context vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for i in range(0,len(pt.contextvars)):
                scv = _str(pt.contextvars[i])
                siv = _str(inst.params[i])
                # if the parameter is an instance reference
                if siv in self.sys.instances():
                    pinst = self.sys.instances[siv]
                    ppt = self.sys.proctypes[pinst.proctype]
                    for x in ppt.localvars:
                        vname = scv + '.' + x.name
                        self.ctable[inst.name][vname] = \
                            self.ctable[pinst.name][x.name]
                # if it's another instance's var reference
                elif '.' in siv:
                    ii,vv = split('.',1)
                    self.ctable[inst.name][siv] = self.ctable[ii][vv]
                # else it's a boolean value or an integer
                else:
                    assert isBool(siv) or isInt(siv)
                    self.ctble[inst.name][siv] = self.compileBOOLorINT(siv)
    #.......................................................................
    def compileSystem(self):
        """
            Compiles the whole system except for the properties.
        """
        self.save(FILEHEADER, False, True)
    #.......................................................................
    def comment(self, string):
        """
            Returns a NuSMV comment string representing 'string'
        """
        return "--" + string
    #.......................................................................
    def save(self, string, tablevel = True, enter = True):
        """
            Saves string into the compiled system string. Adds '\n' to the end
            if enter is True. Adds self.tl to the start if tablevel is True.
        """
        if tablevel:
            self.compiledString += str(self.tl)
            
        self.compiledString += string
        
        if enter:
            self.compiledString += "\n"
    #.......................................................................
    # saveSysToFile:
    #   .. _file: Opened file where to write the compile system
    #   .. props: List of integers, representing the index of the compiled 
    #             properties we wan't to right ass well to the file. Value 
    #             '[-1]' will write all the properties to the file.
    def saveSysToFile(self, _file, props = []):
        """
            Write the compiled system (and optionally the compiled properties)
            to '_file'
        """
        pass
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
