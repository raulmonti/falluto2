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
import shutil
#
#
#===============================================================================
# Default working file name, for data shearing with NuSMV.
#
WORKINGFILE = "temp/"
EMAIL = "mail@mail.com"
#
#==============================================================================#
# LOCAL FUNCTIONS =============================================================#
#==============================================================================#

def parse_input():
    """ Falluto command line input parsing using argparse library. """
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

#===============================================================================
def run_subprocess(command, shell = False, universal_newlines = True):
    """ Launch subprocess, open pipe and get output 
        value and message using subprocess library.
    """
    process = subprocess.Popen(command, shell=shell, stdout=subprocess.PIPE, \
              stderr=subprocess.STDOUT, universal_newlines=universal_newlines)
    output = process.communicate()
    retcode = process.poll()
    if retcode:
        raise subprocess.CalledProcessError(retcode, output[0])
    return output[0]

#===============================================================================
def print_falluto_log():
    print   """
 .----------------.  
| .--------------. |
| |  _________   | |
| | |_   ___  |  | |
| |   | |_  \_|  | |
| |   |  _|      | |
| |  _| |_       | |
| | |_____|ALLUTO| |
| |           2.1| |
| '--------------' |
 '----------------' 
"""


#===============================================================================
def fixme():
    """ Important issues to solve in Falluto """
#    LCRITICAL("Program counters are bigger than needed.")
    LCRITICAL("Bounded traces, or minimal traces for counterexamples.")

#==============================================================================#
# MAIN ========================================================================#
#==============================================================================#

if __name__ == '__main__':
    """ Falluto2.0 main process. """
    # Fixme issues before starting (only in debug level)
    fixme()

    # Print Falluto2.0 header
    print_falluto_log()
    print ( " -- Running FaLLuTO2.0 " + str(datetime.today())\
          + "\n -- " + EMAIL)

    # Parse command line input
    args = parse_input()
    print " -- Input file %s"%args.filename+"\n"

    # Check for existence of input file
    if not os.path.exists(args.filename):
        LERROR("File <" + args.filename + "> doesn't exists.")
        raise Error("File <" + args.filename + "> doesn't exists.")
    elif not os.path.isfile(args.filename):
        LERROR( "Path <"+ str(args.filename) +"> is not a valid file to "\
              + "parse :S.")
        raise Error( "Path <"+ str(args.filename) +"> is not a valid file to "\
                   + "parse :S.")
    # Run
    try:
        # get a copy of the original file to work on.
        _fpath = TEMP_DIR__+'/'+args.filename.split('/')[-1]
        LDEBUG("Working model file at: "+ _fpath)
        shutil.copy2(args.filename, _fpath)

        # set our working file
        while(True): 
            WORKINGFILE = 'temp/'+str(datetime.today().microsecond) + '.smv'
            if not os.path.isfile(WORKINGFILE):
                LDEBUG("Our working file is: "+WORKINGFILE)
                break

        # Get a compiler and a trace interpreter.
        c = Compiler.Compiler()
        t = TraceInterpreter.TraceInterpreter()

        # Get the model parsed as a pyPEG.Symbol structure
        _ppmodel = pyPEG.parse( GrammarRules.GRAMMAR
                              , fileinput.input(_fpath)
                              , False, packrat = False)

        # Sintax replacement dough to definitions (also checks definitions).
        LDEBUG("Precompiling ...")
        SyntaxRepl.precompile(_ppmodel, _fpath+".precompiled")
        if args.save:
            shutil.copy2(_fpath+".precompiled", args.save+".precompiled")
        LDEBUG("Precompiled ;)")

        # Parse the sintax replaced file, and get the model in our own 
        # structures.
        LDEBUG("Parsing ...")
        _model = Parser.parse(_fpath+".precompiled")
        LDEBUG("Successfuly parsed ;)")

        # Check for correctness in the user model of the system.
        LDEBUG("Checking model ...")
        Checker.check(_model)
        LDEBUG("The model is valid ;)")

        # Compile to NuSMV.
        LDEBUG("Compiling ...")
        c.compile(_model)
        LDEBUG("Compiled ;)")

        # Low level debug
        logging.log(logging.INSPECT,\
                    'The compiled model:\n' + c.compiled.string + '\n')
        logging.log(logging.INSPECT,'The compiled properties:\n')
        for p in c.compiled.props:
            logging.log(logging.INSPECT,p) 

        # CHECK DESCRIPTION ON NuSMV
        # Checking the smv system descripition: just run NuSMV over the 
        # system description without checking any property on it.
        sysname = _model.name if _model.name != "" else "No Name System"
        LDEBUG("Checking Model <" + sysname + "> on NuSMV.")
        #get the smv model description
        c.buildModel("",os.path.abspath(WORKINGFILE))
        # save if asked for
        if args.save:
            shutil.copy2(os.path.abspath(WORKINGFILE), args.save)
        # Check the smv system description (raises subprocess.CalledProcessError
        # if NuSMV encounters that the descripton is incorrect).
        output = run_subprocess(["NuSMV", os.path.abspath(WORKINGFILE)])
        LDEBUG(sysname + " model works great for NuSMV ;)")
        if args.color:
            colorPrint("debugGREEN", "[OK] " + sysname + " is OK!\n\n")
        else:
            LINFO(sysname + ' is OK!\n')

        # MODEL CHECK FOR EACH PROPERTY
        #for each property
        for _pname, _p in _model.getProperties().iteritems():
            LINFO("Checking propertie '"+ _pname + "' ...")
            #construct model and place it in WORKINGFILE for NuSMV to read
            c.buildModel(_pname,os.path.abspath(WORKINGFILE))
            #save if asked so
            if args.save:
                shutil.copy2(os.path.abspath(WORKINGFILE), args.save+"."+_pname)
            # Run the model checker.
            output = run_subprocess(["NuSMV", os.path.abspath(WORKINGFILE)])
            # Interpret result and print user readible output.
            t.interpret(c,output,_pname,args.color)            

    except Exception, e:
        if DEBUG__:
            LEXCEPT("")
        elif type(e) == subprocess.CalledProcessError:
            LCRITICAL("Algo anduvo bien mal aca, escribir error en alguna lado"\
                + " y mandar mail a raul para que lo arregle\n")
            LCRITICAL("NUSMV: el archivo es erroneo. La salida es la que "\
                + "sige:\n\n" + str(e.cmd))
        elif type(e) == Error:
            LERROR(e)
        elif type(e) == Critical:
            LCRITICAL(":S something very bad happened.")
        else:
            LEXCEPT("Exception caught :S " + str(type(e)) + "\n" + str(e))

    finally:
        # remove file working copies
        if os.path.exists(_fpath):
            os.remove(_fpath)
        if os.path.exists(_fpath+".precompiled"):
            os.remove(_fpath+".precompiled")
        if os.path.exists(WORKINGFILE):
            os.remove(WORKINGFILE)

    sys.exit(0)
