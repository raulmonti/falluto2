################################################################################
class BaseException():
    def __init__(self):
        self.error = ""
    def __str__(self):
        return str(self.error)
    def __repr__(self):
        return repr(self.error)
    def __unicode__(self):
        return unicode(self.error)


################################################################################
class LethalException(BaseException):
    def __init__(self, error):
        BaseException.__init__(self)
        assert isinstance(error, unicode)
        self.error = error


################################################################################
class UndeclaredError(BaseException):
    def __init__(self, var, line):
        BaseException.__init__(self)
        self.var = str(var)
        self.line = str(line)
        self.error = "Undeclared variable <" + self.var + "> at line <" \
                   + self.line + ">."


################################################################################
class NotBoolExpresionError(BaseException):
    def __init__(self, expr = ""):
        BaseException.__init__(self)
        self.error = "This is not a bool expresion: <" + expr + ">."




################################################################################
class WrongTypeError(BaseException):
    def __init__(self, var, istype = "", isnttype = ""):
        BaseException.__init__(self)
        self.var = var
        self.istype = istype
        self.isnttype = isnttype
        self.error = "Var \'" + str(var) + " is type < " + str(istype) \
                   + " > and should be type < " + str(isnttype) + " >."


################################################################################
class EventNotAllowedError(BaseException):
    def __init__(self):
        BaseException.__init__(self)


################################################################################
class WrongComparisonError(BaseException):
    def __init__(self, vname1, tname1, vname2, tname2, line = -1):
        BaseException.__init__(self)
        self.var1 = vname1
        self.var2 = vname2
        self.type1 = tname1
        self.type2 = tname2
        self.line = line
        self.error = "Wrong comparison between \'" \
                   + str(vname1) + "\' of type < " + str(tname1) + " > and \'" \
                   + str(vname2) + "\' of type < " + str(tname2) + " >."






