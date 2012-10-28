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
from Checker import *
import Checker
#
#===============================================================================

# MODULE PLAIN API =============================================================
# TODO Media al pedo la API???
# Compile:
#   .. system: Parser.System type object to compile.
#   .. @ returns: A Compiler instance with the compiled system.
def Compile(system):
    _cmp = Compiler()
    _cmp.compile(system)
    return _cmp

#===============================================================================




# THE COMPILER =================================================================

class Compiler(object):
    """
    """

    # 
    FILEHEADER = \
    """********** F A L L U T O 2.0 COMPILED SYSTEM FOR NuSMV **********\n\n"""

    #
    __glinst = "Glob#inst"

    # Some names for the compiled system
    __actvar = "action#"   #action variable 
    __dkact  = "dk#action" #deadlock action name (part of the actionvar domain)
    

    def __init__(self):
        self.compiledstring     = ""
        self.compiledproperties = []

        self.sys                = None
        self.tl                 = TabLevel()

        self.ctable             = {}    # 3 levels map: inst->var->compiledVar
        self.varSet             = set([])   # all program variables set.
    #.......................................................................
    def compile(self, system):
        assert isinstance(system, Parser.System)
        self.sys = system
        self.fillVarCompilationTable()
        self.compileSystem()
    #.......................................................................
    # VerifyPropertie:
    #   .. i: propertie index
    def VerifyPropertie(self, i):
        pass
    #.......................................................................
    def fillVarCompilationTable(self):
        # local vars
        self.ctable[Compiler.__glinst] = {}
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            self.ctable[inst.name] = {}
            for lv in pt.localvars:
                self.ctable[inst.name][lv.name] = \
                    self.compileLocalVar(inst.name, lv.name)
                # global instance for properties and contraints compilation
                self.ctable[Compiler.__glinst][inst.name + '.' + lv.name] = \
                    self.ctable[inst.name][lv.name]
                if lv.type == Types.Symbol:
                    # Symbol values
                    for x in lv.domain:
                        self.ctable[inst.name][x] = self.compileSymbValue(x)
                        # global instance again
                        self.ctable[Compiler.__glinst][x] = \
                            self.ctable[inst.name][x]


        # context vars
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for i in range(0,len(pt.contextvars)):
                scv = _str(pt.contextvars[i])
                siv = _str(inst.params[i])
                # if the parameter is an instance reference
                if siv in self.sys.instances:
                    pinst = self.sys.instances[siv]
                    ppt = self.sys.proctypes[pinst.proctype]
                    for x in ppt.localvars:
                        vname = scv + '.' + x.name
                        self.ctable[inst.name][vname] = \
                            self.ctable[pinst.name][x.name]
                # if it's another instance's var reference
                elif '.' in siv:
                    ii,vv = siv.split('.',1)
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
        self.save(self.comment(Compiler.FILEHEADER), False, True)
        self.save("MODULE main()\n")
        self.tl.i()
        self.buildVarSection()
        self.buildInitSection()
        self.buildTransSection()
        self.tl.d()
    #.......................................................................
    def buildVarSection(self):
        self.save(self.comment( " @@@ VARIABLES DECLARATION SECTION." ))
        self.save("VAR")
        self.tl.i()
        # action variable
        lst = set([]) 
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            # faults
            for fault in pt.faults:
                lst.add(self.compileFaultActionVar(inst.name, fault.name))
            n = len(pt.contextvars)
            # transitions
            for act in pt.transitions:
                if not act.name in [_str(x) for x in pt.synchroacts]:
                    lst.add(self.compileAction(inst.name, act.name))
            # Synchro actions
            for act in [_str(x) for x in inst.params[n::]]:
                lst.add(self.compileSynchroAct(act))
            # BIZ effects
            for f in pt.faults:
                if f.type == Types.Byzantine:
                    lst.add(self.compileBizEffect(inst.name, f.name))
            # deadlock action
            lst.add(Compiler.__dkact)
        # save
        self.save(Compiler.__actvar + ':' + self.compileSet(lst) + ';')

        # local variables
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for var in pt.localvars:
                if var.type == Types.Bool:
                    vname = self.ctable[inst.name][var.name]
                    self.save(vname + ":boolean;")
                else:
                    self.save(self.compileAST( inst.name, var.rawinput \
                                             , False) + ';')
        # fault activity variables
        for inst in self.sys.instances.itervalues():
            pt = self.sys.proctypes[inst.proctype]
            for f in pt.faults:
                name = self.compileFaultActive(inst.name, f.name)
                self.save( name + ":boolean;")
        self.tl.d()
    #.......................................................................
    def buildInitSection(self):
        self.save("\n\n")
        self.save(self.comment( " @@@ INITIALIZATION SECTION." ))
        self.save("INIT")
        self.tl.i()
        lst = []
        flst = []
        for inst in self.sys.instances.itervalues():
            pk = self.sys.proctypes[inst.proctype]
            # instance initialization
            lst.append(self.compileAST(inst.name, pk.init, True))
            # faults activation var initialization
            for fault in pk.faults:
                flst.append( self.compileFaultActive(inst.name,fault.name) \
                            + " = FALSE")
        lst.append(self.symbolSeparatedTupleString(flst, False, False))
        self.save(self.symbolSeparatedTupleString(lst, False, True))
        self.tl.d()

    #.......................................................................
    def buildTransSection(self):
        self.save("\n\n")
        self.save(self.comment( " @@@ TRANSITION SECTION." ))
        self.save("TRANS")
        self.tl.i()
        #TODO
        self.tl.d()
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
            self.compiledstring += str(self.tl)
            
        self.compiledstring += string
        
        if enter:
            self.compiledstring += "\n"
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
    def symbolSeparatedTupleString(self, array, parent = True, enter=False, \
                                     amp = '&'):
        parentopen = ""
        parentclose = ""
        amperson = " " + amp + " "
        if parent:
            parentopen = "("
            parentclose = ")"
        if enter:
            amperson = amperson + "\n" + str(self.tl)

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

    # COMPILATION METHODS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    #.......................................................................
    def compileLocalVar(self, iname, vname):
        return "lvar#" + iname + "#" + vname
    #.......................................................................
    def compileSymbValue(self, x):
        return "sv#" + x
    #.......................................................................
    def compileFaultActionVar(self, iname, fname):
        return "fault#" + iname + '#' + fname
    #.......................................................................
    def compileAction(self, iname, actname):
        return "trans#" + iname + "#" + actname
    #.......................................................................
    def compileSynchroAct(self, saname):
        return "synchro#" + saname
    #.......................................................................
    def compileBizEffect(self, iname, fname):
        return "bizE#" + iname + '#' + fname
    #.......................................................................
    def compileSet(self, _set):
        lst = list(_set)
        if lst == []:
            return "{}"
        string = "{ " + str(lst[0])
        for x in lst[1::]:
            string += ', ' + str(x) 
        return string + '}'
    #.......................................................................
    def compileAST(self, iname, ast, space = True):
        sp = ""
        if space:
            sp = " "
        string = ""
        for x in _cl(ast):
            try:
                string += self.ctable[iname][x] + sp
            except:
                string += x + sp
        return string
    #.......................................................................
    def compileFaultActive(self, iname, fname):
        return "factive#" + iname + '#' + fname
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #.......................................................................
    #~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    #.......................................................................

# TESTING ======================================================================
if __name__ == "__main__":
    
    # Reed file from input
    _file = fileinput.input()
    # Parse file
    _sys = Parser.parse(_file)
    # Check ths system correcteness
    chkr = Checker.Checker()
    chkr.check(_sys)
    # Compile to Nusmv
    _cmpsys = Compile(_sys)
    debugLBLUE(_cmpsys.compiledstring)
    
