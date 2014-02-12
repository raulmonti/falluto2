#!/usr/bin/env python
#
#===============================================================================
# Modulo: Falluto2.0.py (Proyect main module)
# Autor: Raul Monti
# Miercoles 23 de Octubre del 2012
#===============================================================================
#
import sys, os
import subprocess
import fileinput
from Exceptions import *
from Debug import *
import pyPEG
from pyPEG import parseLine
import Config
import Parser
import Checker
import Compiler
import TraceInterpreter
import Mejoras
from datetime import datetime
import argparse
import logging
import SyntaxRepl
import GrammarRules
#
#
# ------------------------------------------------------------------------------
#
# Default working file name, for data shearing with NuSMV.
#
WORKINGFILE = "temp/output.smv"
EMAIL = "mail@mail.com"
#
#===============================================================================

#==============================================================================#
# LOCAL FUNCTIONS =============================================================#
#==============================================================================#

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
def printFallutoLog():
    print   """
 .----------------.  
| .--------------. |
| |  _________   | |
| | |_   ___  |  | |
| |   | |_  \_|  | |
| |   |  _|      | |
| |  _| |_       | |
| | |_____|ALLUTO| |
| |           2.0| |
| '--------------' |
 '----------------' 
"""

#==============================================================================#
# MAIN ========================================================================#
#==============================================================================#

if __name__ == '__main__':
    """
        Falluto2.0 main process.
    """
    printFallutoLog()
    # Print Falluto2.0 header
    print ( " -- Running FaLLuTO2.0 " + str(datetime.today())\
          + " --\n -- " + EMAIL)

    # Parse input to this module
    args = parseInput()

    print " -- Input file %s"%args.filename+"\n"

    # Check for existence of input file
    if not os.path.exists(args.filename):
        LERROR("File <" + args.filename + "> doesn't exists.\n")
        sys.exit(0)

    # Run
    try:
        # Get a compiler and a trace interpreter.
        c = Compiler.Compiler()
        t = TraceInterpreter.TraceInterpreter()

        # Get the model parsed as a pyPEG.Symbol structure
        _ppmodel = pyPEG.parse( GrammarRules.GRAMMAR
                              , fileinput.input(args.filename)
                              , False, packrat = False)

        # Sintax replacement dough to definitions (also checks definitions).
        LINFO("Precompiling ...")
        SyntaxRepl.precompile(_ppmodel, args.filename+".precompiled")
        LINFO("Precompiled ;)")

        # Parse the sintax replaced file, and get the model in our own 
        # structures.
        LINFO("Parsing ...")
        _model = Parser.parse(args.filename+".precompiled")
        LINFO("Successfuly parsed ;)")

        # Check for correctness in the user model of the system.
        LINFO("Checking model ...")
        Checker.Check(_model)
        LINFO("The model is valid ;)")

        exit(0)

        # Compile to NuSMV.
        c.compile(_model)

        # Checking the smv system descripition: just run NuSMV over the 
        # system description without checking any property on it.
        sysname = _model.name if _model.name != "" else "No Name System"
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

    except Exception, e:
        if DEBUG__:
            LEXCEPTION(e)
        elif type(e) == subprocess.CalledProcessError:
            LCRITICAL("Algo anduvo bien mal aca, escribir error en alguna lado y "\
                + "mandar mail a raul para que lo arregle\n")
            LCRITICAL("NUSMV: el archivo es erroneo. La salida es la que "\
                + "sige:\n\n" + str(e.cmd))
        elif type(e) == Error:
            LERROR(e)
        elif type(e) == Critical:
            LCRITICAL(":S something very bad happened.")
        else:
            LEXCEPTION("Exception caught :S " + str(type(e)) + "\n" + str(e))

    sys.exit(0)

