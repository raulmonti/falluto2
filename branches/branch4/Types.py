class Types():

    # var types
    Int = 0
    Bool = 1
    Symbol = 2
    Reference = 3
    
    # fault types
    Transient = 54
    Stop = 55
    Byzantine = 56
    
    Types = { 0:"Int"           # variables
            , 1:"Bool"
            , 2:"Symbol"
            , 3:"Reference"
            , 54:"Transient"    # faults
            , 55:"Stop"
            , 56:"Byzantine"
            }

    def __init__(self):
        pass
