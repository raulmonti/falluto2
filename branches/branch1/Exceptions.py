#===============================================================================
# Modulo Exceptions.py
# 8 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

from pyPEG import Symbol


class RongComparisonERROR(Exception):
    def __init__(self, ast, t1, t2, mssg = ""):
        Exception.__init__(self)
        assert isinstance(ast, Symbol)
        self.rep = ast
        self.line = ast.__name__.line
        self.t1 = t1
        self.t2 = t2
        self.message = mssg
    def __unicode__(self):
        error = "Rong comparison between " + self.t1 + " and " + self.t2 \
              + " in line: " + self.line + "\n\n" + self.message
        return unicode(error)
    def __repr__(self):
        return self.__unicode__()        
    def __str__(self):
        return self.__unicode__()        



class RedeclaredError(Exception):
    def __init__(self, repeated, where):
        Exception.__init__(self)
        self.rep = repeated
        self.where = where
    def __unicode__(self):
        error = "Redeclared " + self.rep + " in lines: "
        for x in self.where:
            error += x + " "
        return unicode(error)
    def __repr__(self):
        return self.__unicode__()        
    def __str__(self):
        return self.__unicode__()        
        
class NoInstancesError(Exception):
    def __init__(self):
        Exception.__init__(self)
    def __unicode__(self):
        return unicode("Error: No instances where declared. The systeme is" \
                     + " not valid.")
    def __repr__(self):
        return self.__unicode__()
    def __str__(self):
        return self.__unicode__()
        
  
class UndeclaredError(Exception):
    def __init__(self, v):
        Exception.__init__(self)
        self.value = v
        assert isinstance(v, Symbol)

    def __unicode__(self):
        error = "Undeclared value " + str(self.value.what) + " at line: " \
              + str(self.value.__name__.line)
        return unicode(error)
    def __repr__(self):
        return self.__unicode__()  
    def __str__(self):
        return self.__unicode__()


class InvalidSymbolError(Exception):
    def __init__(self, s):
        Exception.__init__(self)
        self.value = s
        assert isinstance(s, Symbol)
    def __unicode__(self):
        error = "Invalid symbol < " + self.value.what + " > at line: "\
              + self.value.__name__.line
        return unicode(error)
    def __repr__(self):
        return self.__unicode__()        
    def __str__(self):
        return self.__unicode__()       


class MyTypeError(Exception):
    def __init__(self, exp  = None, istype = "", nottype = [], iname = ""):
        Exception.__init__(self)
        self.error = repr(exp) + " is type " + istype \
                   + " and should be of a type in " + repr(nottype) \
                   + ", while instansing " + iname
        self.exp = exp
        self.istype = istype
        self.nottype = nottype

    def __unicode__(self):
        return unicode(self.error)
    def __repr__(self):
        return self.__unicode__()        
    def __str__(self):
        return self.__unicode__()       


class CiclicDeclarationError(Exception):
    def __init__(self, inst = None):
        Exception.__init__(self)
        self.line = inst.line
        self.iname = inst.name
        self.error = "Cant use self variables to pass as "\
                   + "context variable at instance " \
                   + self.iname + " at line " + self.line
    def __unicode__(self):
        return unicode(self.error)
    def __repr__(self):
        return self.__unicode__()        
    def __str__(self):
        return self.__unicode__()       

