
class Compiled():
    """ Structure with the compiled system info. Along with useful methods to
        build up the NuSMV model.
    """
    def __init__(self):
        self.string = ""    #the full model
        self.props = {}     #properties
        self.vars = {}      #variable declarations
        self.faults = {}    #faults
        self.init = ""      #initial states formula
        self.trans = {}     #transitions
        self.constrs = {}   #constraints
        self.defines = {}   #definitions
        self.tab = ""       #tabbing inside the file

    #===========================================================================
    def adddef(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.defines
        self.defines[name] = self.makeCompiled(name,comment,compiled);

        # TODO CHECK THERE ARE NO 2 PROPERTIES WITH THE SAME NAME
    def addprop(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.props
        if name == "":
            name = '@prop#'+str(len(self.props))
        self.props[name] = self.makeCompiled(name,comment,compiled);
    
    def addvar(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.vars
        if name == "":
            name = '@var#'+str(len(self.vars))
        self.vars[name] = self.makeCompiled(name,comment,compiled);

    def addfault(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.faults
        if name == "":
            name = '@fault#'+str(len(self.faults))
        self.faults[name] = self.makeCompiled(name,comment,compiled);

    def addinit(self, i):
        assert isinstance(i, str) # don't forgget connector at the begining
        self.init += ' ' + i        

    def addtrans(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.trans
        if name == "":
            name = '@trans#'+str(len(self.trans))
        self.trans[name] = self.makeCompiled(name,comment,compiled);

    def addconstr(self, name="", comment="", compiled=""):
        assert name != None
        assert not name in self.constrs
        if name == "":
            name = '@constr#'+str(len(self.constrs))
        self.constrs[name] = self.makeCompiled(name,comment,compiled);

    #===========================================================================
    def makeCompiled(self, n="", c="", cd=""):
        """ """
        return {'name':n, 'comm':c, 'cpld':cd } #name, comment, compiled

    #===========================================================================
    def buildModel(self, addinit="", addtrans=[], propname=""):
        """ Build the full model, store it in string and also return it.
            @param 'addinit': string formula to append to the init section. Be
                              sure to include the connective at the beggining.
            @param 'addtrans': string formula to append to the tran section. Be
                               sure to include the connective at the beggining.
            @param 'props': properties to check in the model.
        """

        self.writeHeader()
        self.writeModuleStart()
        self.it()
        self.writeDefinitions()
        self.writeVarSection()
        self.writeInitSection()
        self.writeTransSection()
        self.dt()
        self.writeConstraints()
        return self.string


    #===========================================================================
    def writeHeader(self):
        # HEADER
        self.write( "-- (-.-) F A L L U T O 2.0 " \
                  + "COMPILED SYSTEM FOR NuSMV (-.-) --\n\n")

    #===========================================================================
    def writeDefinitions(self):
        # DEFINITIONS
        self.comment("@-@-@-@-@-@-@ DEFINITIONS\n")
        for d,v in self.defines.iteritems():
            self.comment("@ DEFINITION " + str(d) + ":\n")
            self.writeln(v['cpld'])
        self.writest("\n")
        

    #===========================================================================
    def writeModuleStart(self):
        # NuSMV Module starts here
        self.writeln("MODULE main()\n")

    #===========================================================================
    def writeVarSection(self):
        # VAR SECTION
        self.comment("@ VARIABLES SECTION\n")
        self.writeln("VAR")
        self.it()
        for v in self.vars.itervalues():
            self.writeln(v['cpld'])
        self.writest("\n")
        self.dt()

    #===========================================================================
    def writeInitSection(self):
        # INIT SECTION
        self.comment("@ INIT SECTION\n")
        self.writeln("INIT")
        self.it()
        self.writeln(self.init)
        self.writest("\n")
        self.dt()

    #===========================================================================
    def writeTransSection(self):
        # TRANSITIONS SECTION
        self.comment("@ TRANS SECTION\n")
        self.writeln("TRANS")
        self.it()
        lst = list(self.trans.itervalues())
        self.writeln("( " + lst[0]['cpld'])
        for t in lst[1:]:
            self.writeln("| " + t['cpld'])
        self.writeln(")")
        self.writest("\n")
        self.dt()
    
    #===========================================================================
    def writeConstraints(self):
        # CONSTRAINTS
        self.comment("@-@-@-@-@-@-@ CONTRAINTS\n")
        for c,v in self.constrs.iteritems():
            self.comment("@ CONSTRAINT " + c + ":\n")
            self.writeln(v['cpld'])
        self.writest("\n")

    #===========================================================================
    # Building helpers =========================================================
    #===========================================================================

    def it(self, inc=1):
        """ Increment tabulation. """
        for i in range(0,inc):            
            self.tab += '    '

    def dt(self, dec=1):
        """ Decrement tabulation. """
        dec = min(dec, len(self.tab))
        for i in range(0,dec):
            self.tab = self.tab[:-4]

    def comment(self, string):
        """
            Returns a NuSMV comment string representing 'string'
        """
        return "--" + string

    def write(self, string=""):
        """  """
        #TODO
        self.string += self.tab + string
    
    def writeln(self, string=""):
        """ """
        #TODO
        self.write(string+"\n")

    def writest(self, string=""):
        """ (Write) string into self.string but (s)caping from (t)ab level """
        self.string += string

    #===========================================================================
    # TO FILE ==================================================================
    #===========================================================================

    def writeSysToFile(self, filename):
        """ Write the compiled system (and optionally the compiled properties)
            to '_file'

            @ filename: Name of the file to create and write.
        """
        #open file and truncate at beginning
        fileOutput = open(filename, 'w+')                       
        fileOutput.write(self.string)
        fileOutput.close()

