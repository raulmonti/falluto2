"""
    Raul Monti 30 agosto 2012
    
    Modulo encargado de interpretar las trazas devueltas por NuSMV a partir del
    archivo generado por Falluto.
    
"""


import InputManager.pyPEG
from InputManager.pyPEG.pyPEG import keyword, _and, _not, ignore
import re
from Debug import *
from Config import *
from Compiler import TabLevel, Names


debugTODO("Que pasa cuando una synchro action sincroniza con mas de una "\
        + "accion de un mismo modulo, como saber con cual sincronizo?")

debugURGENT("Interpretar warnings de NuSMV. Recordar lo de espacio de estados iniciales vacios por un mal ltlspec")

#===============================================================================
class SpecificationResult():

    def __init__(self):
        self.specification = ""
        self.result = false
        self.trace = []
        
    def parse(self, ast):
        pass
        




#===============================================================================        
""" For printig whith colors :D 
    Put CR|CB|CG|CY before the text you want to color, and CE after it.
"""

CS = '\033['
CE = '\033[1;m'
CR = CS + '1;31m' #red start printing
CB = CS + '1;94m' #blue start printing
CG = CS + '1;32m' #green start printing
CY = CS + '1;33m' #yellow start printing



#===============================================================================        

string_state_start = \
"--|-------------------------------------------------------------------------->"
string_state_end = string_state_start

string_spec_end = \
"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"

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

    def tprint(self, string, enter = True):
        if enter:
            print self.tab, string
        else:
            print self.tab, string,
            
    def interpret(self, ast, cosys, specindex):
        self.cosys = cosys
        self.sys = cosys.sys


        specrepr = cosys.properties[specindex][0]
        #no hace falta este for, deberia ser una unica especification
        for sp in ast:
            if sp.__name__ == "TRUESPEC":
                print CG + "|+|\tSpecification " + CE + CY + str(specrepr) \
                    + CE + CG  + " is true\n\n" + CE


            if sp.__name__ == "FALSESPEC":
                print CR + "|-|\tSpecification " + CE + CY + str(specrepr) \
                    + CE + CR  + " is false\n\n" + CE \
                    + "\tas demonstrated by the following execution sequence:\n"
                self.tab.i()
                self.interpret_trace(sp.what[1])
                self.tab.d()
    
    
    #.......................................................................
    def interpret_trace(self, ast):
        ast = ast.what
        self.showaction = False          # so we don't show the first action
        self.stateN = 0
        for state in ast:
            #interpret state
            if state.__name__ == "STATE":
                self.interpret_state(state)
            if state.__name__ == "STATELOOP":
                self.tprint( CR + "\n\t<<<<<<<<<<<<<<<<<<<<  ...  Loop starts" \
                        + " here  ...  >>>>>>>>>>>>>>>>>>>>\n\n" +CE)
                for st in state.what:
                    self.interpret_state(st)

        self.tprint(CR + string_spec_end + CE)
        print "\n\n"
    #///////////////////////////////////////////////////////////////////////    


    #.......................................................................
    def interpret_state(self, state):
        state = state.what
        self.showstate = True
        
        # Get the state properties changes on the new state. Also update the
        # action variable and other parameters.
        # First value in State is the state number the rest are var changes.
        varchs = self.get_var_changes(state[1::])

        # Show the action that brought us to this state
        self.interpret_action()

        self.tab.i()
        # Show the state
        if self.showstate:
            # Show the new state
            print "" #just a neline in the output
            self.tprint(CY+string_state_start+CE)
            self.tprint(CY + "  |" + CE, False)
            print "\t-> State: " + str(self.stateN) + " <-"
            self.tprint(CY + "  |" + CE)
            self.tprint(CY + "  |" + CE, False)
            print "\tCHANGES FROM LAST STATE:"
            self.tprint(CY + "  |\n" + CE, False)
          
            #now we show the changes in this new state:
            for vch in varchs:
                self.tprint(CY + "  |" + CE, False)
                print "\t" + self.interpret_local_var(vch)

            self.tprint(CY+string_state_end+CE)
            print ""
            self.stateN += 1

        self.tab.d()
        # To start showing actions after the first state has past:
        self.showaction = True 
    #///////////////////////////////////////////////////////////////////////
    

    """
        Interpret and output the actual state of self.action.
    """
    def interpret_action(self):
       
        head = self.action.split("#",1)[0]
        if not self.showaction:
            return
        # If it's a deadlock transition
        if self.action == Names.dkaction:
            if not self.sysdk:
                # System has falled in deadlock (we don't show next state, and
                # we advise the user.
                self.tprint(CR+ "System falled in deadlock !!!!\n" + CE)
                self.showstate = False
                self.sysdk = True
                return
        
        # If it's a fault transition        
        elif head == "lfault":
            self.interpret_fault_action()
        
        
        elif head == "synchro":
            self.tprint(self.interpret_synchro_action())
            
        elif head == "lact":
            self.tprint(self.interpret_local_action())  
                      
        elif head == "bizE":
            self.tprint(self.interpret_biz_efect_action())
              
        else:
            raise TypeError("Unknown variable head: " + head)
        
        self.showstate = True
        self.sysdk = False
    #///////////////////////////////////////////////////////////////////////



    """
        Get the string correponding to the representation of the ocurrence of
        a bizantine efect action.
        @ uses: self.action to get the bizantine efect action ocurrence.
    """
    def interpret_biz_efect_action(self):
        nothing, inst, name = self.action.split("#",2)
        return "Bizantine efect action from bizantine fault " + CB + \
            name + CE + " of instance " + CB + inst + CE





    #///////////////////////////////////////////////////////////////////////

    """
        Get the string correponding to the representation of the ocurrence of
        a local action.
        @ uses: self.action to get the local action ocurrence.
    """
    def interpret_local_action(self):
        la = self.action.split("#",1)[1]
        lainst, laname = la.split("#",1)
        return "Local action " +CB+ laname +CE+ " of instance " +CB+ lainst +CE
    #///////////////////////////////////////////////////////////////////////



    """
        Get the string correponding to the representation of the ocurrence of
        a synchronization action.
        @ uses: self.action to get the synchronization action ocurrence.
    """
    def interpret_synchro_action(self):
        sa_name = self.action.split("#",2)[1]
        string = "Synchronization action " +CB+ sa_name +CE+ " synchronizing: "
        flag = False
        for iname in self.cosys.syncdict[sa_name]:
            inst = self.sys.instances[iname]
            mod = self.sys.modules[inst.module]
            for i in range(0,len(inst.params)):
                if inst.params[i] == sa_name:
                    i -= len(mod.contextVars)
                    act_name = mod.synchroActs[i]
                    if flag:
                        string += " | "
                    string += iname + "[" + mod.name + "/" + act_name + "]"
                    break
            flag = True
        return string
    #///////////////////////////////////////////////////////////////////////




    """
        Get the string correponding to the representation of the ocurrence of
        a fault.
        @ uses: self.action to get the fault ocurrence.
    """
    debugTODO("Deberua devolver el string y no imprimirlo")
    def interpret_fault_action(self):
        h,i,f = self.action.split("#",3)
        inst = self.sys.instances[i]
        mod = self.sys.modules[inst.module]
        for fault in mod.faults:
            if fault.name == f:
                self.tprint("[action] Instance " + CB + i + CE + " fault " \
                    + CB + f + CE + " of type " + fault.faulttype + ".", False)
                if fault.faulttype == "STOP":
                    if fault.efects == []:
                        print "Stops all the instance"
                    else:
                        print "Stops transitions " \
                            + str([str(x) for x in fault.efects]) \
                            + " from this module."
                print ""
                break
    #///////////////////////////////////////////////////////////////////////


    """
        Get the string corresponding to the representetaion of a local variable
        state.
    """
    def interpret_local_var(self, lvar):
        h,i,v = lvar[0].split("#",3)
        return "* Instance " + CB + i + CE + " local var " + CB + v + CE \
                + CY + " = " + CE + CG + str(lvar[1]) + CE 





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
            if Names.actionvar in vch:
                self.action = vch[0] if vch[0] != Names.actionvar else vch[1]
            
            # update active faults
            elif "factive" in heads:
                vch = self.order(vch,"factive")
                if vch[1] == "TRUE":
                    self.activefaults.append(vch[0])
            
            # append local var change to the resulting list
            elif "lvar" in heads:
                res.append(self.order(vch,"lvar"))

        return res






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

def SYS():          return -1, ignore(r"(?!--).*\n"), -1, [TRUESPEC, FALSESPEC]
def TRUESPEC():     return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("true")
def FALSESPEC():    return "--", keyword("specification"), re.compile(r".*(?=is)"), "is", keyword("false"), TRACE
def TRACE():        return -1, ignore(r"(?!->).*\n"), -1 , STATE, -1, STATELOOP
def STATE():        return "->", "State:", re.compile(r"\d*\.\d*"), "<-", -1 , VARCHANGE
def VARCHANGE():    return re.compile(r"[a-zA-Z0-9\#\_]*"), "=", re.compile(r"[a-zA-Z0-9\#\_]*")
def STATELOOP():    return "--", "Loop", "starts", "here", -1, STATE



debugURGENT("Averiguar que significa que haya dos 'Loop starts here' uno " \
          + "desp del otro, como en el caso de abajo")
"""
-- specification  G inst1#var1 != TRUE  is false
-- as demonstrated by the following execution sequence
Trace Description: LTL Counterexample 
Trace Type: Counterexample 
-> State: 2.1 <-
  action# = inst1#f2
  inst1#f1#active = FALSE
  inst1#f2#active = FALSE
  inst1#var1 = TRUE
-- Loop starts here
-> State: 2.2 <-
  action# = dk#action
-> State: 2.3 <-
  action# = inst1#f1
-- Loop starts here
-> State: 2.4 <-
  action# = dk#action
-> State: 2.5 <-
  action# = inst1#f1
-> State: 2.6 <-
  action# = dk#action
"""


