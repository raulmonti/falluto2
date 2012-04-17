from sintaxChecker.interpreter import interpret

class System():
    def __init__(self):
        pass


class Var():
    def __init__(self):
        self.type = ""
        self.domain = []
        self.name = ""


class Module():

    def __init__(self):
        self.name = ""
        self.contextVars = []
        self.contextActs = []
        self.localVars = []
        self.actions = []

    def hasVar(self, v):
        return v in self.localVars

    def printMe(self):

        print "MODULE", self.name

        print "\t. PARAMETRIC VARIABLES:",
        for x in self.contextVars:
            print x,
        print "\n",

        print "\t. PARAMETRIC ACTIONS:",
        for x in self.contextActs:
            print x,
        print "\n",

        print "\t. LOCAL VARS:"
        for x in self.localVars:
            print "\t\t-", x.name, x.type, x.domain
        print "\n",


class Parser():

    def __init__(self):
        self.interpreted = interpret()
        self.system = None

    def retriveSystem(self):
        return self.system

    def parse(self):
        result = True
        
        for x in self.interpreted:
            if x.__name__ == 'MODULE':
                m = self.parseModule(x.what)
                print "MODULE found: "
                m.printMe()
            elif x.__name__ == 'INSTANCE':
                pass
            else:
                pass

        return result


    def parseModule(self, module):
        m = Module()
        for x in module:
            if x.__name__ == 'IDENT':
                m.name = x.what
            elif x.__name__ == 'CONTEXTVARS':
                for v in x.what:
                    m.contextVars.append(v.what)
            elif x.__name__ == 'CONTEXTACTS':
                for a in x.what:
                    m.contextActs.append(a.what)
            elif x.__name__ == 'MODULEBODY':
                for e in x.what:
                    if e.__name__ == 'VAR':
                        for v in e.what:
                            var = Var()
                            v = v.what
                            var.name = v[0].what
                            var.type = v[1].__name__
                            var.domain = v[1].what
                            m.localVars.append(var)
                    else: 
                        pass
            else:
                pass

        #print "DEBUG: ", module[0].__name__.line
        return m



if __name__ == '__main__':
    p = Parser()
    print "-----------------------------------------------------------------\n"\
    , "PARSING RESULT\n",\
    "-----------------------------------------------------------------\n"
    r = p.parse()
    print "\nThe parsing resulted:", r, "\n"
    print "=================================================================\n"

