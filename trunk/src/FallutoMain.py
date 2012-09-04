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

    print( "\033[1;94m\nHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH"\
         + "HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH\nFaLLuTO " \
         + "2 . 0 : 31 Agosto 2012\n\n\033[1;m")

    files = fileinput.input()

    if not files:
        debugERROR("No input file!!! :S")

    try:
        p = Parser.Parser()
        c = Compiler()
        t = TraceInterpreter.TraceInterpreter()
        sys = p.parse(files)
        c.compile(sys, "outcompilertest")                        
        
        for i in range(0, len(c.properties)):
            outputfile = c.smv_file_builder(i)    
            output = check_output(["NuSMV", os.path.abspath(outputfile)])
            #debugCURRENT(output)
            (res, rest) = parseLine(output, TraceInterpreter.SYS(), [], True)
            if rest != "":
                debugERROR("Error al interpretar las trazas. No se pudo " \
                        + "interpretar lo que sigue:\n\n"  + rest)
            t.interpret(res, c)
        
    except NoInstancesError, e:
        colorPrint('debugYELLOW', e)
    
    except subprocess.CalledProcessError, e:
        debugERROR("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debugERROR("NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))

