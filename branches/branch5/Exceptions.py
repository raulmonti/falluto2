from Types import *
from Utils import _str, putBrackets


################################################################################
class BaseException():
    def __init__(self):
        self.error = ""
        self.cause = ""
    def __str__(self):
        return str(self.error)
    def __repr__(self):
        return repr(self.error)
    def __unicode__(self):
        return unicode(self.error)


################################################################################
class LethalE(BaseException):
    def __init__(self, error):
        BaseException.__init__(self)
        #assert isinstance(error, unicode)
        self.error = str(error)


################################################################################
class UndeclaredError(BaseException):
    def __init__(self, var):
        BaseException.__init__(self)
        self.var = str(var)
        self.error = "Undeclared variable \'" + self.var + "\'."


################################################################################
class NotBoolExpresionError(BaseException):
    def __init__(self, expr = ""):
        BaseException.__init__(self)
        self.error = "This is not a bool expresion: \'" + expr + "\'."


################################################################################
class NotMathExpresionError(BaseException):
    def __init__(self, expr = ""):
        BaseException.__init__(self)
        self.error = "This is not a math expresion: \'" + expr + "\'."


################################################################################
class WrongTypeError(BaseException):
    def __init__(self, var, istype = "", isnttype = ""):
        BaseException.__init__(self)
        self.var = var
        self.istype = istype
        self.isnttype = isnttype
        self.error = "Var \'" + str(var) + "\' is type < " + str(istype) \
                   + " > and should be type < " + str(isnttype) + " >."


################################################################################
class EventNotAllowedE(BaseException):
    def __init__(self, event):
        BaseException.__init__(self)
        self.cause = _str(event)


################################################################################
class NextRefNotAllowedE(BaseException):
    def __init__(self, nextref):
        BaseException.__init__(self)
        self.cause = _str(nextref)


################################################################################
class WrongTFO(LethalE): #wrong types for operand
    def __init__(self, t1, t2, operand, where, line):
        t1s = ""
        t2s = ""
        exp = ""
        try:
            t1s = Types.Types[t1]
            t2s = Types.Types[t2]
            exp = putBrackets(where)
        except:
            pass

        raise LethalE( "Wrong types <" + t1s + "> and <" + t2s \
                     + "> for operand \'" + str(operand)
                     + "\' in expresion \'" + exp + "\', at <" 
                     + str(line) + ">.")
################################################################################


