from pyPEG import Symbol


class FallutoBaseException(Exception):
    def __init__(self):
        Exception.__init__(self)
        self.name = "No name"
        self.line = -1
        self.error = "No error"
    
    def __unicode__(self):
        return unicode(self.error)
    def __repr__(self):
        return self.__unicode__()  
    def __str__(self):
        return self.__unicode__()


class EmptyASTError(Exception):
    def __init__(self):
        Exception.__init__(self)


  
class UndeclaredError(FallutoBaseException):
    def __init__(self, name, line, iname):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.iname = iname
        self.error = "Undeclared symbol " + name + " at line " + str(line) \
                   + ", while instancing << " + iname + " >>."



class RedeclaredName(Exception):
    def __init__(self, name, line):
        Exception.__init__(self)
        self.name = name
        self.line = line
        self.error = "Redeclared Name " + name + " at line " + str(line)
    
    def __unicode__(self):
        return unicode(self.error)
    def __repr__(self):
        return self.__unicode__()  
    def __str__(self):
        return self.__unicode__()


class RedeclaredFault(RedeclaredName):
    def __init__(self, faultname, line):
        RedeclaredName.__init__(self, faultname, line)
        self.error = "Redeclared Fault " + name + " at line " + str(line)


class CantUseEventsError(FallutoBaseException):
    def __init__(self, name = "", line = -1):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.error = "Cant use Events in <<" + name + ">>, at line " + str(line)

class InstHasNoActionError(FallutoBaseException):
    def __init__(self, iname, actname, line):
        self.iname = iname
        self.actname = actname
        self.line = line
        self.error = "Error at line " + str(line) + ". Instance <<" + iname \
                   + ">> has no action named <<" + actname + ">>."

class WrongRangeError(FallutoBaseException):
    def __init__(self, name = "", line = -1):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.error = "Wrong range declaration at line " + str(line)\
                   + ". First limit should be smaller or equal to the second "\
                   + "one."

class MyTypeError(FallutoBaseException):
    def __init__(self, name, istype, needtype, line, iname):
        FallutoBaseException.__init__(self)
        self.iname = iname
        self.name = name
        self.line = line
        self.error = name + " should be type " + str(needtype) \
                   + " and is type " + str(istype) + ", at line " \
                   + str(line) + " while instancing << " + iname + " >>."


class WrongComparisonError(FallutoBaseException):
    def __init__(self, name, type1, type2, line, iname):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.type1 = type1
        self.type2 = type2
        self.iname = iname
        self.error = "Wrong comparisson between " + type1 + " and " + type2 \
                   + ", on << " + name + " >>, at line " + str(line) \
                   + ", while instancing << " + iname + " >>."


class InvalidSymbolError(FallutoBaseException):
    def __init__(self, name, line, iname):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.iname = iname
        self.error = "Error at line " + str(line) \
                   + ". Symbol << " + name + " >> has not been defined."


class InvalidNextAssignError(FallutoBaseException):
    def __init__(self, name, value, type1, type2, line, iname):
        FallutoBaseException.__init__(self)
        self.name = name
        self.line = line
        self.iname = iname
        self.error = "Cant assign value " + value + " of type " + type2 \
                   + " to next state of variable " + name + " of type " \
                   + type1 + ", in line " + str(line) \
                   + ", while instancing << " + iname + " >>."
