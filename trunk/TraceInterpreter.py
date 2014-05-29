"""
    Raul Monti 30 agosto 2012
    
    Modulo encargado de interpretar las trazas devueltas por NuSMV a partir del
    archivo generado por Falluto.
    
"""
import pyPEG
from pyPEG import keyword, _and, _not, ignore, parseLine
import re
from Debug import *
from Config import *
from Utils import TabLevel, ast2str, ast2lst
from Compiler import Compiler
from Types import Types
import os


#TODO ver como da nusmv el output cuando hay mas de un modulo para sacar ideas
#TODO opcion para mostrar todas las variables en cada estado
#TODO revisar por que a veces no muestra el deadlock (fijarse si al principio
# guarda el valor de dkaction mas alla de no mostrarlo).

#===============================================================================
class SpecificationResult():

    def __init__(self):
        self.specification = ""
        self.result = false
        self.trace = []
        
    def parse(self, ast):
        pass
        

#===============================================================================        

"""
CS = TraceInterpreter.CS
CE = TraceInterpreter.CE
CR = TraceInterpreter.CR
CB = TraceInterpreter.CB
CG = TraceInterpreter.CG
CY = TraceInterpreter.CY
"""



string_state_start = "--|----------------->"
string_state_end = string_state_start

string_spec_end = \
"\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"

# For printig whith colors :D 
# Put CR|CB|CG|CY before the text you want to color, and CE after it.

COLOR__ = False



class TraceInterpreter():

    def __init__(self):
        self.tab = TabLevel()
        self.showstate = True
        self.action = ""
        self.stateN = 0
        self.sysdk = False
        self.activefaults = []
        self.cosys = None
        self.sys = None
        self.ignoreaction = False
        self.CS = ""
        self.CE = ""    #end color
        self.CR = ""    #red start printing
        self.CB = ""    #blue start printing
        self.CG = ""    #green start printing
        self.CY = ""    #yellow start printing

    #.......................................................................
    def tprint(self, string, enter = True):
        if enter:
            print str(self.tab) + string
        else:
            print str(self.tab) + string,
    #.......................................................................
    def interpret(self, cosys, trace, specindex, color = False):

        if not color:
            self.CS = ""
            self.CE = ""
            self.CR = ""
            self.CB = ""
            self.CG = ""
            self.CY = ""
        else:
            self.CS = '\033['
            self.CE = '\033[1;m'
            self.CR = self.CS + '1;31m'
            self.CB = self.CS + '1;94m'
            self.CG = self.CS + '1;32m'
            self.CY = self.CS + '1;33m'

        self.cosys = cosys
        self.sys = cosys.sys

        (ast, rest) = parseLine(trace, RESULT(), [], True, packrat=True)

        if rest != "":
            debugCURRENT(ast)
            debugERROR( "Error al interpretar las trazas. No se pudo " \
                      + "interpretar lo que sigue:\n\n"  + rest)
            os._exit(1)

        specrepr = cosys.compiled.props[specindex]['comm']
        specname = cosys.compiled.props[specindex]['name']
        for sp in ast:
            if sp.__name__ == "TRUESPEC":
                print self.CG + "|+| - Specification " + self.CE + self.CY \
                    + str(specname) + "\n    - " + specrepr + self.CE + self.CG\
                    + "\n    - is true" + self.CE

            elif sp.__name__ == "FALSESPEC":
                print self.CR + "|-| - Specification " + self.CE + self.CY \
                    + str(specname)  + "\n    - " + specrepr\
                    + self.CE + self.CR  + "\n    - is false" + self.CE \
                    + "\n    - as demonstrated by the following execution"\
                    + " sequence:\n"
                self.tab.i()
                self.interpret_trace(sp.what[1])
                self.tab.d()

            elif sp.__name__ == "WARNING":
                warning = self.interpret_warning(sp)
                if warning != "":
                    self.tprint(self.CR \
                          + "<<<<  WARNING FOR NEXT TEST CASE: >>>>\n"\
                          + warning + self.CE)
            elif sp.__name__ == "NUSMVHEADER":
                pass # we don't do nothing with the header 
            else:
                raise TypeError(sp.__name__)
    #.......................................................................

    """
        Interpret the NuSMV warning and return the string representing the
        interpretation.
    """
    def interpret_warning(self, ast):
        if 'single-value variable' in str(ast.what):
            return ""
        else:
            return str(ast.what)

    #.......................................................................
    def interpret_trace(self, ast):
        ast = ast.what
        self.ignoreaction = True          # so we don't show the first action
        self.stateN = 0
        for state in ast:
            #interpret state
            if state.__name__ == "STATE":
                self.interpret_state(state)
            if state.__name__ == "STATELOOP":
                print self.CG + "\n>> Loop starts here <<\n" + self.CE
                for st in state.what:
                    self.interpret_state(st)

        self.tprint(self.CR + string_spec_end + self.CE)


    #.......................................................................
    """
        
    """    
    def interpret_state(self, state):
        state = state.what
        self.showstate = True
        
        # Get the state properties changes on the new state. Also update the
        # action variable and other parameters.
        # First value in State is the state number the rest are var changes.
        varchs = self.get_var_changes(state[1::])

        # Show the action that brought us to this state
        trans = self.interpret_action()
        if trans != None and trans != "":
            print "@ " + trans + ""

        # Show the state
        if self.showstate:
            # Show the new state
            print "" #just a neline in the output
            #self.tprint(self.CY+string_state_start+self.CE)
            print "---> State: " + str(self.stateN) + " <---"
          
            #now we show the changes in this new state:
            for vch in varchs:
                print "  " + self.interpret_var(vch)

            #self.tprint(self.CY+string_state_end+self.CE)
            print ""
            self.stateN += 1

        # To start showing actions after the first state has past:
        self.ignoreaction = False 


    #.......................................................................
    """
        Interpret and output the actual state of self.action.
    """
    def interpret_action(self):
       
        if self.ignoreaction:
            return

        head = self.action.split("#",1)[0]

        # If it's a deadlock transition
        if self.action == Compiler._dkact:
            if not self.sysdk:
                # System has fell in deadlock (we don't show next state, and
                # we advise the user.
                self.showstate = False
                self.sysdk = True
                return self.CR+ self.sys.name + " fell in deadlock !!!!"+self.CE
        
        else:
            # If it's a fault transition
            self.showstate = True
            self.sysdk = False

            if head == "fault":
                return self.interpret_fault_action()
            
            elif head == "synchro":
                return self.interpret_synchro_action()
                
            elif head == "trans":
                return self.interpret_local_action()
                          
            elif head == "byzE":
                return self.interpret_byz_efect_action()
                  
            else:
                raise TypeError("Unknown variable head: " + head)
        



    #.......................................................................
    """
        Get the string correponding to the representation of the ocurrence of
        a byzantine efect action.
        @ uses: self.action to get the byzantine efect action ocurrence.
    """
    def interpret_byz_efect_action(self):
        nothing, inst, name = self.action.split("#",2)
        return "[byzEffect] " + self.CY + inst + self.CE + " / " \
               + self.CB + name + self.CE



    #.......................................................................
    """
        Get the string correponding to the representation of the ocurrence of
        a local action.
        @ uses: self.action to get the local action ocurrence.
    """
    def interpret_local_action(self):
        nothing, lainst, laname = self.action.split("#",2)
        return "[action] "+self.CY+lainst+self.CE+" / "+self.CB+laname+self.CE



    #.......................................................................
    """
        Get the string correponding to the representation of the ocurrence of
        a synchronization action.
        @ uses: self.action to get the synchronization action ocurrence.
    """
    def interpret_synchro_action(self):
        sa_name = self.action.split("#",2)[1]
        string = "[Synchro] " + self.CB + sa_name + self.CE + " ["
        flag = False

        _set = set([])
        for iname, lst in self.cosys.syncToTrans[sa_name].iteritems():
            for t in lst:
                _set.add((iname, t.name))
                
        for (iname,tname) in _set:
            if flag:
                string += " || "
            string += iname + "/" + tname
            flag = True
        return string + "]"




    #.......................................................................
    """
        Get the string correponding to the representation of the ocurrence of
        a fault.
        @ uses: self.action to get the fault ocurrence.
    """

    def interpret_fault_action(self):
        h,i,f = self.action.split("#",3)
        inst = self.sys.instances[i]
        pt = self.sys.proctypes[inst.proctype]
        res = ""
        for fault in pt.faults:
            if fault.name == f:
                res += "[fault] " + self.CY + i + self.CE + " / " +  self.CB \
                    + f + self.CE + " / " + Types.Types[fault.type]
                if fault.type == Types.Stop:
                    if fault.affects != []:
                        res += " "+ str([ast2str(x) for x in fault.affects])
                break

        return res



    #.......................................................................
    """
        Get the string corresponding to the representetaion of a local variable
        state.
    """
    def interpret_var(self, lvar):
        h,i,v = lvar[0].split("#",3)
        
        # if its a symbol value:
        val = str(lvar[1])
        if '#' in val:
            val = val.split('#',1)[1]
        
        return self.CB + i + self.CE + " " + self.CB + v + self.CE \
                + self.CY + " = " + self.CE + self.CG + str(val) + self.CE 


    #.......................................................................
    """
        Get all variable changes in the state that concern to the user, and take
        note of other variable changes like actionvar value and fault values.
        @ return:
            a list with the local vars changes from 'vchlst'.
        @ updates:
            self.action
            self.activefaults
    """
    def get_var_changes(self, vchlst):
        res = []
        for vch in vchlst:
            vch = vch.what
            # the head of each string defines it.
            heads = [(vch[0].split("#", 1))[0],(vch[1].split("#", 1))[0]]
            
            # update action
            if Compiler._actvar in vch:
                self.action = vch[0] if vch[0] != Compiler._actvar else vch[1]
            
            # update active faults
            elif "factive" in heads:
                vch = self.order(vch,"factive")
                if vch[1] == "TRUE":
                    self.activefaults.append(vch[0])
            
            # append local var change to the resulting list
            elif "lvar" in heads:
                res.append(self.order(vch,"lvar"))

        return res



    #.......................................................................
    """
        Orders a varchange (a list of two elements representing the value that 
        takes some variable in some state), placing first the element that 
        starts with 'head'.
    """
    def order(self, vch, head):
        if (vch[0].split("#", 1))[0] == head:
            return vch
        else:
            return vch[::-1]
    
    

#===============================================================================
"""
    Lenguaje PyPEG para interpretar las trazas
"""

def RESULT():   return  NUSMVHEADER, -1, [WARNING, TRUESPEC, FALSESPEC]
    
def NUSMVHEADER():  return 11, re.compile(r".*\n")

def ELSE():     return -1, re.compile(r".*\n")

def WARNING():  return re.compile(r"((?!--|\n).*\n)+")

def TRUESPEC():     return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("true")

def FALSESPEC():    return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("false"), TRACE
def TRACE():        return -1, ignore(r"(?!->|--\ Loop).*\n"), -1 , [STATE, STATELOOP]
def STATE():        return "->", "State:", re.compile(r"\d*\.\d*"), "<-", -1 , VARCHANGE
def VARCHANGE():    return re.compile(r"[\w\d\#\_]*(\[.*\])?"), "=", re.compile(r"\-?[a-zA-Z0-9\#\_]*")
def STATELOOP():    return "--", "Loop", "starts", "here", -1, STATE











