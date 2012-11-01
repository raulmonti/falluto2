#===============================================================================
# Modulo: Falluto2.0.py (modulo principal del proyecto)
# Autor: Raul Monti
# Miercoles 23 de Octubre del 2012
#===============================================================================
#
import sys, os
import subprocess
import fileinput
from Exceptions import *
from Debug import *
from pyPEG import parseLine
import Config
import Parser
import Checker
import Compiler
import TraceInterpreter
import Mejoras #DEBUGTODO__=True en Config.py para ver los debugs de este modulo
#
#===============================================================================


debugTODO("Capturar el WARNING de espacio de estados inciales vacio")

#...............................................................................
def check_output(command, shell = False, universal_newlines = True):
    process = subprocess.Popen(command, shell=shell, stdout=subprocess.PIPE, \
              stderr=subprocess.STDOUT, universal_newlines=universal_newlines)
    output = process.communicate()
    retcode = process.poll()
    if retcode:
        raise subprocess.CalledProcessError(retcode, output[0])
    return output[0]
#...............................................................................

#TODO fecha en python para mostrar en el encabezado del programa

if __name__ == '__main__':

    print( "\033[1;94m\nHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH"\
         + "HHHHHHHHHHHHHHHHHHHHHHHHHHH\nFaLLuTO " \
         + "2 . 0 : 31 Agosto 2012\n\n\033[1;m")

    files = fileinput.input()

    if not files:
        debugERROR("No input file!!! :S")

    outputname = "temp/output.smv"        
    try:
        c = Compiler.Compiler()
        t = TraceInterpreter.TraceInterpreter()
        debugYELLOW("Parsing input...")
        sys = Parser.parse(files)
        debugYELLOW("Compiling the input system...")
        c.compile(sys)                        
        
        sysname = sys.name if sys.name != "" else "No Name System"
        
        #Checking the smv system descripition:
        colorPrint("debugYELLOW", "Checking system: " + sysname)        
        #get the smv system description
        c.writeSysToFile(outputname,[])
        #debugCURRENT(outputfile)
        # Check the smv system description (raises subprocess.CalledProcessError
        # if NuSMV encounters that the descripton is incorrect).
        output = check_output(["NuSMV", os.path.abspath(outputname)])
        #debugCURRENT(output)
        colorPrint("debugGREEN", sysname + " is OK!\n\n")


        for i in range(0, len(c.compiledproperties)):
            c.writeSysToFile(outputname,[i])

            output = check_output(["NuSMV", os.path.abspath(outputname)])
            #debugCURRENT(output)
            (res, rest) = parseLine(output, TraceInterpreter.SYS(), [], True, packrat=True)
            debugGREEN(res)
            if rest != "":
                debugERROR("Error al interpretar las trazas. No se pudo " \
                        + "interpretar lo que sigue:\n\n"  + rest)
            t.interpret(res, c, i)
  
    except subprocess.CalledProcessError, e:
        debugERROR("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debugERROR("NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))

