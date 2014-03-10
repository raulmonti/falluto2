class Types():

    # var types
    Notype = -1
    Int = 0
    Bool = 1
    Symbol = 2
    Array = 3
    IntArray = 4
    BoolArray = 5
    SymbolArray = 6
    #Reference = 3
    
    # fault types
    Transient = 54
    Stop = 55
    Byzantine = 56
    
    # Propertie types
    Ctlspec = 100
    Ltlspec = 105
    Nb      = 110 #normal behaiviour
    Fmf     = 115 #finitely many fault
    Fmfs    = 120 #finitely many faults
    
    # Contraint types
    WFDisable = 151
    FFDisable = 155
    Checkdk   = 165
    Sysname   = 175
    
    
    Types = { 0:"Int"           # variables
            , 1:"Bool"
            , 2:"Symbol"
            , 3:"Array"
            , 54:"Transient"    # faults
            , 55:"Stop"
            , 56:"Byzantine"
            }

    propToType = { "NORMALBEHAIVIOUR":Nb
                 , "FINMANYFAULTS":Fmfs
                 , "FINMANYFAULT":Fmf
                 , "CTLSPEC":Ctlspec
                 , "LTLSPEC":Ltlspec
                 }


    def __init__(self):
        pass


