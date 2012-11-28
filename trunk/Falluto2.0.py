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
from datetime import datetime
import argparse
#
#===============================================================================


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


#...............................................................................
def parseInput():
    parser = \
    argparse.ArgumentParser(prog='Falluto2.0', description='Falluto 2.0 Model Checker Using NuSMV')
    parser.add_argument('--version', action='version', version='%(prog)s version 0.0')
    parser.add_argument('filename', help='Input file path, where the description of the system has been written.')
    parser.add_argument('-s','--s', '-save', help='Path of the file to be written with the NuSMV compiled model of the system.', dest='save', metavar='path')
    parser.add_argument('-co', help='Color output.', action='store_true', dest='color')
    return parser.parse_args()

#...............................................................................

#===============================================================================
if __name__ == '__main__':

    args = parseInput()

    print( "\033[1;94m\n******************************************************"\
         + "*************************\n** FaLLuTO " \
         + "2.0\n** " + str(datetime.today()) + "\n\033[1;m")

    
    files = fileinput.input(args.filename)

    if not files:
        debugERROR("No input file!!! :S")

    outputname = "temp/output.smv"
    try:
        c = Compiler.Compiler()
        t = TraceInterpreter.TraceInterpreter()
        #debugYELLOW("Parsing input...")
        msys = Parser.parse(files)
        #debugYELLOW("Checking system...")
        Checker.Check(msys)
        #debugYELLOW("Compiling the input system...")
        c.compile(msys)

        sysname = msys.name if msys.name != "" else "No Name System"

        #Checking the smv system descripition:
        colorPrint("debugYELLOW", "** Checking system: " + sysname)
        #get the smv system description
        c.writeSysToFile(outputname,[])
        #debugCURRENT(outputfile)
        # Check the smv system description (raises subprocess.CalledProcessError
        # if NuSMV encounters that the descripton is incorrect).
        output = check_output(["NuSMV", os.path.abspath(outputname)])
        #debugCURRENT(output)
        colorPrint("debugGREEN", "** " + sysname + " is OK!\n\n")

        if args.save:
            c.writeSysToFile(args.save,None)

        for i in range(0, len(c.compiledproperties)):
            c.writeSysToFile(outputname,[i])

            output = check_output(["NuSMV", os.path.abspath(outputname)])
#            debugCURRENT(output)
            _color = False
            if args.color:
                _color = True
            t.interpret(c,output, i, _color)
  
    except subprocess.CalledProcessError, e:
        debugERROR("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debugERROR("NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))
    except LethalE as e:
        colorPrint("debugRED", "ERROR:\t" + e.error)

    sys.exit(0)
