from subprocess import call


import sys, os
sys.path.append(os.path.abspath('../../'))

#import subprocess
from GrammarRules2 import SYSTEM, COMMENT
from Parser2 import *
from InputManager.pyPEG.pyPEG import *
from Compiler import Compiler
import fileinput
import Debug
import Config
import traceInterpreter
import subprocess


def check_output(command, shell = False, universal_newlines = True):
    process = subprocess.Popen(command, shell=shell, stdout=subprocess.PIPE, \
              stderr=subprocess.STDOUT, universal_newlines=universal_newlines)
    output = process.communicate()
    retcode = process.poll()
    if retcode:
            raise subprocess.CalledProcessError(retcode, command, output=output[0])
    return output[0]



if __name__ == '__main__':

    files = fileinput.input()
    ast = parse(SYSTEM(), files, True, COMMENT, lineCount = True)
    #Debug.DebugYELLOW( ast)
    sys = System()
    try:
        sys.parse(ast)
        #sys.printMe()
        c = Compiler()
        outputfile = c.compile(sys, "outcompilertest")
        output = check_output(["NuSMV", os.path.abspath(outputfile)])
        #call(["NuSMV", os.path.abspath(outputfile)])
        colorPrint("debugGREEN", output)
        ast = []
        (res, rest) = parseLine(output, traceInterpreter.SYS(), ast, True)
        if rest != "":
            printColor("debugRED", "ERROR al interpretar las trazas :S")
        else:
            print "nusmv result parsing ", res, " and couldnt parse ", rest
            ti = traceInterpreter.TraceInterpreter()
            ti.interpret(res)
        
    except NoInstancesError, e:
        colorPrint('debugYELLOW', e)
    
