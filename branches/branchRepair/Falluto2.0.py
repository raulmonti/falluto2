#!/usr/bin/env python


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
import Mejoras
from datetime import datetime
import argparse
#
#
# ------------------------------------------------------------------------------
#
#
# Default working file name, for data shearing with NuSMV.
#
WORKINGFILE = "temp/output.smv"
#
#
#===============================================================================





################################################################################
def parseInput():
    """
        Falluto command line input parsing using 
        argparse library.
    """
    parser = argparse.ArgumentParser(prog='Falluto2.0', 
        description='Falluto 2.0 Model Checker Using NuSMV')
    parser.add_argument('--version', 
        action='version', 
        version='%(prog)s version 0.0')
    parser.add_argument('filename', 
        help = 'Input file path, where the description of the system has been '\
             + 'written.')
    parser.add_argument('-s','--s', '-save', 
        help = 'Path of the file to be written with the NuSMV compiled model '\
             + 'of the system.', dest='save', metavar='path')
    parser.add_argument('-co', help='Color output.', 
        action='store_true', dest='color')
    return parser.parse_args()
#...............................................................................




################################################################################  
def run_subprocess(command, shell = False, universal_newlines = True):
    """
        Launch subprocess, open pipe and get output 
        value and message using subprocess library.
    """
    process = subprocess.Popen(command, shell=shell, stdout=subprocess.PIPE, \
              stderr=subprocess.STDOUT, universal_newlines=universal_newlines)
    output = process.communicate()
    retcode = process.poll()
    if retcode:
        raise subprocess.CalledProcessError(retcode, output[0])
    return output[0]
#...............................................................................



################################################################################
if __name__ == '__main__':
    """
        Falluto2.0 main process string.
    """
    # Print Falluto2.0 header
    print( "\033[1;94m[]\n[] FaLLuTO " \
         + "2.0\n[] " + str(datetime.today()) + "\n[]\n\033[1;m")

    # Parse input to this module
    args = parseInput()

    # Check for existence of input file
    if not os.path.exists(args.filename):
        ErrorOutput("File <" + args.filename + "> doesn't exists.\n", True)
        sys.exit(0)

    # Open the file
    modelFile = fileinput.input(args.filename)
    assert modelFile

    # Run
    try:
        # Get a compiler and a trace interpreter.
        c = Compiler.Compiler()
        t = TraceInterpreter.TraceInterpreter()

        # Parse de file.
        msys = Parser.parse(modelFile)

        # Check for correctness in the user model of the system.
        Checker.Check(msys)

        # Compile to NuSMV.
        c.compile(msys)



        # Checking the smv system descripition: just run NuSMV over the 
        # system description without checking any property on it.
        sysname = msys.name if msys.name != "" else "No Name System"
        colorPrint("debugYELLOW", "[CHECKING] Checking system: " + sysname)

        #get the smv system description
        c.writeSysToFile(WORKINGFILE,[])

        # Check the smv system description (raises subprocess.CalledProcessError
        # if NuSMV encounters that the descripton is incorrect).
        output = run_subprocess(["NuSMV", os.path.abspath(WORKINGFILE)])

        colorPrint("debugGREEN", "[OK] " + sysname + " is OK!\n\n")



        # Save a copy of the compiled system if asked so.
        if args.save:
            c.writeSysToFile(args.save,None)


        # Check one by one each property over the system.
        for i in range(0, len(c.compiledproperties)):
            # Prepair a file with the system compiled model
            # and the i-th property.
            c.writeSysToFile(WORKINGFILE,[i])

            # Run the model checker.
            output = run_subprocess(["NuSMV", os.path.abspath(WORKINGFILE)])
            
            # Interpret result and print user readible output.
            _color = False
            if args.color:
                _color = True
            # TODO puedo usar args.color como booleano directamente?
            t.interpret(c,output, i, _color)


    except subprocess.CalledProcessError, e:
        debugERROR("Algo anduvo bien mal aca, escribir error en alguna lado y "\
            + "mandar mail a raul para que lo arregle\n")
        debugERROR("NUSMV: el archivo es erroneo. La salida es la que "\
            + "sige:\n\n" + str(e.cmd))

    except Exception, e:
        colorPrint("debugRED", str(type(e)) + "\n" + str(e))

    sys.exit(0)

