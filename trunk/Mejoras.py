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

debugTODO( "Poner parentesis a las expresiones compiladas, por las dudas NuSMV"\
         + " asocie de otra manera los operadores.")

           
debugTODO( """ Permitir renombrar transiciones, tener cuidado de no sincronizar 
con estas transiciones, cambiar el nombre de las renombradas y hacer tabla de 
renombrado por si hay un just(transicion renombrada) en algun lugar del sistema 
de input.""")

debugTODO("Lograr trazas de contraejemplo mas cortas y lindas :D")

debugTODO("Averiguar sobre line-wrapped para que se vea mejor la salida")

debugTODO("instances weak fairness en instancias en particular y no en todas")

debugTODO("Permitir la opcion de encontrar contrajemplos acotados.")

debugTODO("Imprimir valores de los defines en la traza contraejemplo")

debugTODO("Opcion para mostrar el output de NuSMV sin procesar")

debugTODO("El archivo temporal deberia tener nombre unico por cada corrida.")

debugTODO("Crear carpeta temp si es que no existe. Opciones para configurar" \
         +" rutas como la de esta carpeta por ejemplo.")

debugTODO( "Efectos de falla bizantina no deberian apoderarse de la ejecucion" \
         + "por defecto asi como las fallas en gral.")

debugTODO( "Opcion de computar el tiempo que le lleva verificar.")

debugTODO( "Opcion de guardar resultados en un archivo")

debugTODO( "Representar internamente las fallas biz como transient para "\
         + "ahorrar una transicion si es posible (no creo que sea correcto)" )
debugTODO( "Reemplazar en la compilacion tabs por espacios.")
