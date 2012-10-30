#===============================================================================
# Mejoras sugeridas para el programa falluto 2.0
#===============================================================================
#
from Debug import *
#
#===============================================================================
debugTODO("Eliminar las restricciones sintacticas para nombres reservados de "\
         + "falluto, detectarlos en otro lado y devolver un mensaje de error "\
         + "mas expresivo de lo que esta pasando")
        
debugTODO( "En vez de usar el nombre del proceso en el valor proctype de las "\
         + "instancias, usar directamente una referencia las mismas.")
         
debugTODO( "Levantar warning cuando dos asignaciones a una misma next ref en " \
         + "una postcondiciones hacen o pueden hacer imposible la transicion " \
         + "o la ocurrencia de la falla o lo que sea.")

debugTODO( "Controlar mejor las inclusiones (no se puede bool en symbolic set)"\
         + "por ejemplo, mientras que en falluto lo estamos aceptando")

debugTODO( "Poner parentesis a las expresiones compiladas, por las dudas NuSMV"\
         + " asocie de otra manera los operadores.")
