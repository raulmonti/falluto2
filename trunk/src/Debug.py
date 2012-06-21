# MODULE Debug
# 9 de Junio del 2012
# Autor: Raul Monti


debugColorDict = {
    'debugRED'    : '1;31m',
    'debugGREEN'  : '1;32m',
    'debugYELLOW' : '1;33m',
    'debugMAGENTA': '1;45m',
    'debugLBLUE'  : '1;94m',
    'debugTODO'   : '1;45m'
}

def Debug(color, string):
    print '\033[' + debugColorDict[color] + "DEBUG: " +  str(string) + '\033[1;m'
    
def DebugTODO(string):
    print '\033[' + debugColorDict['debugTODO'] + "TODO: " + string + '\033[1;m'

def DebugRED(string):
    print '\033[' + debugColorDict['debugRED'] + "DEBUG: " + string + '\033[1;m'
