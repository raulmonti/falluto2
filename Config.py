# MODULO DE CONFIGURACION PARA FALLUTO 2.0
# 9 de Junio del 2012
# Autor: Raul Monti

import os
import logging
import sys

#==============================================================================#
# MODULES GLOBAL VARS =========================================================#
#==============================================================================#

DEBUG__ = True

DEBUGTODO__ = False

NICEOUTPUT__ = False

TRACEBACKLIMIT__ = 10 # for critical errors traceback

LOGLEVEL__ = logging.INFO

#==============================================================================#
# GLOBAL PATHS ================================================================#
#==============================================================================#

TEMP_DIR__ = os.path.dirname(os.path.realpath(__file__)) + "/temp"

LOG_FILE__ = os.path.dirname(os.path.realpath(__file__)) + "log.log"

#==============================================================================#
# LOGGING =====================================================================#
#==============================================================================#
#    logging.basicConfig(filename='logfile.log', level=logging.DEBUG)
#    Logging levels:
#    CRITICAL 50
#    ERROR    40
#    WARNING  30
#    INFO     20
#    DEBUG    10
#    NOTSET   0

# adding a new level to logger
logging.INSPECT = 5 
logging.addLevelName(logging.INSPECT, "LOOK ")

# My own formatter
class MyFormatter(logging.Formatter):
    err_fmt  = "[    %(levelname)s    ] %(msg)s"
    dbg_fmt  = "[    %(levelname)s    ] %(module)s: %(lineno)d: %(msg)s"
    info_fmt = "[    %(levelname)s    ] %(msg)s"
    cri_fmt = "[    FIXME!    ] %(msg)s"
    war_fmt = "[    %(levelname)s    ] %(msg)s"

    def __init__(self, fmt="%(levelno)s: %(msg)s"):
        logging.Formatter.__init__(self, fmt)

    def format(self, record):

        # Save the original format configured by the user
        # when the logger formatter was instantiated
        format_orig = self._fmt

        # Replace the original format with one customized by logging level
        if record.levelno == logging.DEBUG:
            self._fmt = MyFormatter.dbg_fmt

        elif record.levelno == logging.INFO:
            self._fmt = MyFormatter.info_fmt

        elif record.levelno == logging.ERROR:
            self._fmt = MyFormatter.err_fmt

        elif record.levelno == logging.CRITICAL:
            self._fmt = MyFormatter.cri_fmt

        elif record.levelno == logging.WARNING:
            self._fmt = MyFormatter.war_fmt

        # Call the original formatter class to do the grunt work
        result = logging.Formatter.format(self, record)

        # Restore the original format configured by the user
        self._fmt = format_orig

        return result

# config logger
fmt = MyFormatter()
hdlr = logging.StreamHandler(sys.stdout)
hdlr.setFormatter(fmt)
logging.root.addHandler(hdlr)
logging.root.setLevel(LOGLEVEL__)

# Definitions for logger
LERROR = logging.error
LWARNING = logging.warning
LINFO = logging.info
LDEBUG = logging.debug
LEXCEPT = logging.exception
LCRITICAL = logging.critical

