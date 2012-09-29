################################################################################
# Module Typing.py
# For Falluto 2.0 Model check front end
#
# Raul Monti
# lun 24 Septiembre 2012
#
# Module in charge of the typing system
#
################################################################################


from pyPEG import Symbol, parseLine
from Exceptions import *
from Debug import *


################################################################################        

class Types():
    Unknown = -1
    Bool = 0
    Int = 1
    Symbol = 2
    
    types = ["Bool","Int","Symbol"]

    def __init__(self):
        pass


