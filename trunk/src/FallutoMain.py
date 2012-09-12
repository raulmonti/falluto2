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
debugTODO("Capturar el WARNING de espacio de estados inciales vacio")


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
         + "HHHHHHHHHHHHHHHHHHHHHHHHHHH\nFaLLuTO " \
         + "2 . 0 : 31 Agosto 2012\n\n\033[1;m")

    files = fileinput.input()

    if not files:
        debugERROR("No input file!!! :S")

    try:
        p = Parser.Parser()
        c = Compiler()
        t = TraceInterpreter.TraceInterpreter()
        debugYELLOW("Parsing input...")
        sys = p.parse(files)
        debugYELLOW("Compiling the input system...")
        c.compile(sys, "outcompilertest")                        
        
        sysname = \
        sys.options.sysname if sys.options.sysname != "" else "No Name System"
        
        #Checking the smv system descripition:
        colorPrint("debugYELLOW", "Checking system: " + sysname)        
        #get the smv system description
        outputfile = c.smv_file_builder(-1)
        #debugCURRENT(outputfile)
        # Check the smv system description (raises subprocess.CalledProcessError
        # if NuSMV encounters that the descripton is incorrect).
        output = check_output(["NuSMV", os.path.abspath(outputfile)])
        #debugCURRENT(output)
        colorPrint("debugGREEN", sysname + " is OK!\n\n")

        
        for i in range(0, len(c.properties)):
            outputfile = c.smv_file_builder(i)
            #debugCURRENT(outputfile)
            output = check_output(["NuSMV", os.path.abspath(outputfile)])
            #debugCURRENT(output)
            (res, rest) = parseLine(output, TraceInterpreter.SYS(), [], True, packrat=True)
            if rest != "":
                debugERROR("Error al interpretar las trazas. No se pudo " \
                        + "interpretar lo que sigue:\n\n"  + rest)
            t.interpret(res, c, i)
        
    except NoInstancesError, e:
        colorPrint('debugYELLOW', e)
    
    except subprocess.CalledProcessError, e:
        debugERROR("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debugERROR("NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))

