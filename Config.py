# MODULO DE CONFIGURACION PARA FALLUTO 2.0
# 9 de Junio del 2012
# Autor: Raul Monti

import os
import logging

#==============================================================================#
# MODULES GLOBAL VARS =========================================================#
#==============================================================================#

DEBUG__ = True

DEBUGTODO__ = False

DEBUGURGENT__ = True

DEBUGCURRENT__ = True

DEBUGSOLVED__ = False

DEBUGSMV__ = False

NICEOUTPUT__ = False

TRACEBACKLIMIT__ = 10 # for critical errors traceback

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

logging.INSPECT = 5 
logging.addLevelName(logging.INSPECT, "LOOK ")
logging.basicConfig( level=logging.INSPECT
                   , format = '[    %(levelname)s    ] ' \
                            + '[%(filename)s %(lineno)s] %(message)s')

LERROR = logging.error
LWARNING = logging.warning
LINFO = logging.info
LDEBUG = logging.debug
LEXCEPTION = logging.exception
LCRITICAL = logging.critical
def LINSPECT(msg):
    logging.log(logging.INSPECT, msg)
