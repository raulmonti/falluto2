import sys, os
import subprocess
import fileinput
from Exceptions.Exceptions import *
from Compiler import Compiler
from Debug import *
from InputManager.pyPEG.pyPEG import parseLine
import Config
import TraceInterpreter
import Parser

debugURGENT("Revisar por que no anda la inclusion de pyPEG.pyPEG :S")



def check_output(command, shell = False, universal_newlines = True):
    process = subprocess.Popen(command, shell=shell, stdout=subprocess.PIPE, \
              stderr=subprocess.STDOUT, universal_newlines=universal_newlines)
    output = process.communicate()
    retcode = process.poll()
    if retcode:
        raise subprocess.CalledProcessError(retcode, output[0])
    return output[0]



if __name__ == '__main__':

    files = fileinput.input()

    try:
        sys = Parser.parse(files)
        c = Compiler()
        outputfile = c.compile(sys, "outcompilertest")
        print os.path.abspath(outputfile)
        output = check_output(["NuSMV", os.path.abspath(outputfile)])
        debugCURRENT(output)
        ast = []
        (res, rest) = parseLine(output, TraceInterpreter.SYS(), ast, True)
        if rest != "":
            colorPrint("debugRED", "ERROR al interpretar las trazas :S\n\n" + rest)
        else:
            if rest != "":
                debugCURRENT("nusmv result parsing "+str(res) \
                           + " and couldnt parse "+str(rest))
            ti = TraceInterpreter.TraceInterpreter(c)
            ti.interpret(res)
        
    except NoInstancesError, e:
        colorPrint('debugYELLOW', e)
    
    except subprocess.CalledProcessError, e:
        debugTODO("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debug("debugRED", "NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))

