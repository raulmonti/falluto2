#===============================================================================
# Modulo Exceptions.py
# 8 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

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
