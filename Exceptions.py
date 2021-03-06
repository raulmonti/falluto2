# Moduel Exceptions
# Author Raul
# 07/02/2014 14:18:14 

import traceback
from Config import TRACEBACKLIMIT__
from Types import *
from Utils import ast2str, putBrackets


################################################################################
class BaseException(Exception):
    def __init__(self,error="", cause="", where=""):
        self.error = error
        self.cause = cause
        self.where = where
    def __str__(self):
        return str(unicode(self))
    def __repr__(self):
        return repr(unicode(self))
    def __unicode__(self):
        result = unicode(self.error) + "\n"
        if self.cause != "":
            result += "   in: " + unicode(self.cause)
        if self.where != "":
            result += "\n   at: " + unicode(self.where)
        return result

################################################################################
class LethalE(BaseException):
    def __init__(self, error):
        BaseException.__init__(self)
        #assert isinstance(error, unicode)
        self.error = str(error)

################################################################################
class Error(BaseException):
    def __init__(self, error, cause="", where=""):
        BaseException.__init__(self,error,cause,where)

################################################################################
class Critical(BaseException):
    def __init__(self, error):
        BaseException.__init__(self)
        self.error = str(error)



################################################################################
class UndeclaredError(BaseException):
    def __init__(self, var):
        BaseException.__init__(self)
        self.cause = str(var)
        self.error = "Undeclared variable \'" + self.cause + "\'."


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
        t1s = Types.Types[t1]
        t2s = Types.Types[t2]
        exp = putBrackets(where)

        raise Error( "Wrong types <" + t1s + "> and <" + t2s \
                   + "> for operand \'" + str(operand)
                   + "\' in expresion \'" + exp + "\', at <" 
                   + str(line) + ">.")
################################################################################
class SysError():
    def __init__(self):
        self.error = ""
    def __str__(self):
        return str(self.error)
    def __unicode__(self):
        return unicode(self.error)
    def __repr__(self):
        return repr(self.error)
################################################################################



    

