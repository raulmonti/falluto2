# MODULE Debug
# 9 de Junio del 2012
# Autor: Raul Monti

import inspect, sys
from Config import *

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
    'debugTODO'   : '1;45m',
    'debugURGENT' : '1;41m'
}


debugStart = "\n===============================================================\n"
debugEnd = "\n_______________________________________________________________\n\n"


def debug(color, string):
    print '\033[' + debugColorDict[color] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'


    



def debugRED(string):
    if DEBUG__:
        print '\033[' + debugColorDict["debugRED"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass

def debugGREEN(string):
    if DEBUG__:
        print '\033[' + debugColorDict["debugGREEN"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass

def debugYELLOW(string):
    if DEBUG__:
        print '\033[' + debugColorDict["debugYELLOW"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass


def debugLBLUE(string):
    if DEBUG__:
        print '\033[' + debugColorDict["debugLBLUE"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass

def debugMAGENTA(string):
    if DEBUG__:
        print '\033[' + debugColorDict["debugMAGENTA"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass

def debugURGENT(string):
    if DEBUGURGENT__:
        print '\033[' + debugColorDict['debugURGENT'] + "URGENT: [" + str(lineno()) + "]: " +  str(string) + '\033[1;m'
    else:
        pass
    


def debugCURRENT(string):
    if DEBUGCURRENT__:
        print '\033[' + debugColorDict['debugLBLUE'] + "\n-----------------    CURRENT DEBUG: [" + str(lineno()) + "]: " + "\n\n" + str(string) + "\n\n-----------------    END CURRENT DEBUG\n" '\033[1;m'
    else:
        pass

def debugSOLVED(string):
    if DEBUGSOLVED__:
        print '\033[' + debugColorDict["debugMAGENTA"] + "DEBUG: [" + str(lineno())  + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'
    else:
        pass


#
# PROGRAM DEBUG
#

def WARNING(string):
    print '\033[' + debugColorDict["debugYELLOW"] + "WARNING: [" + str(lineno())  + "]:\n" + str(string) + '\033[1;m',


def debugERROR(string):
    print '\033[' + debugColorDict["debugRED"] + "ERROR: [" + str(lineno()) \
          + "]: " + debugStart + str(string) + debugEnd + '\033[1;m'

def debugTODO(string):
    if DEBUGTODO__:
        print '\033[' + debugColorDict['debugTODO'] + "TODO: [" + str(lineno())\
              + "]: " + str(string) + '\033[1;m'
    else:
        pass

#
# COLOR PRINTING ...............................................................
#

def colorPrint(color, string, enter=True):
    if enter:
        print '\033[' + debugColorDict[color] + str(string) + '\033[1;m'
    else:
        print '\033[' + debugColorDict[color] + str(string) + '\033[1;m',
