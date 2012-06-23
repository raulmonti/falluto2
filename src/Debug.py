# MODULE Debug
# 9 de Junio del 2012
# Autor: Raul Monti

import inspect, sys

def lineno():
    frame = inspect.currentframe()
    frame = frame.f_back.f_back
    line  = frame.f_lineno
    code  = frame.f_code
    name  = code.co_filename
    return name + " " + str(line)


debugColorDict = {
    'debugRED'    : '1;31m',
    'debugGREEN'  : '1;32m',
    'debugYELLOW' : '1;33m',
    'debugMAGENTA': '1;45m',
    'debugLBLUE'  : '1;94m',
    'debugTODO'   : '1;45m'
}

def Debug(color, string):
    print '\033[' + debugColorDict[color] + "DEBUG: [" + str(lineno())  + "]: " + str(string) + '\033[1;m'
    
def DebugTODO(string):
    print '\033[' + debugColorDict['debugTODO'] + "TODO: [" + str(lineno()) + "]: " + str(string) + '\033[1;m'

def DebugRED(string):
    print '\033[' + debugColorDict['debugRED'] + "DEBUG: [" + str(lineno()) + "]: " +  str(string) + '\033[1;m'

def DebugGREEN(string):
    print '\033[' + debugColorDict['debugGREEN'] + "DEBUG: [" + str(lineno()) + "]: " +  str(string) + '\033[1;m'

def DebugYELLOW(string):
    print '\033[' + debugColorDict['debugYELLOW'] + "DEBUG: [" + str(lineno()) + "]: " +  str(string) + '\033[1;m'
