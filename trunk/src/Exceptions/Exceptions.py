#===============================================================================
# Modulo Exceptions.py
# 8 de Junio del 2012
# Autor: Raul Monti
#===============================================================================

class RedeclaredError(Exception):
    def __init__(self, repeated, where):
        self.rep = repeated
        self.where = where
    def __unicode__(self):
        error = "Redeclared " + self.rep + " in lines: "
        for x in self.where:
            error += x + " "
        return unicode(error)
