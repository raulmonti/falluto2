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
    Ltlspec = 101
    Nb      = 102 #normal behaiviour
    Fmf     = 103 #finitely many fault
    Fmfs    = 104 #finitely many faults
    Ensure  = 105
    Atmost  = 106
    
    # Contraint types
    WFDisable = 151
    FFDisable = 155
    Checkdk   = 165
    Modname   = 175
    
    
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
                 , "ENSURE":Ensure
                 , "ATMOST":Atmost
                 }


    def __init__(self):
        pass


