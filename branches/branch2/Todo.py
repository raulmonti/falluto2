#
#   Listado de TODO's del proyecto Falluto 2.0
#       
#



from Debug import *
from Config import *


debugSOLVED("Cambiar precondiciones vacias por TRUE en el parser."        \
            + "Solution: kakasa, directly changed precondition value for" \
            + " [True] :s Better solution will be to make a PyAST and "   \
            + "call for the propform parse method in the preconditions."  )



debugTODO("Revisar si es buena idea lo del pseudo ENUM de la clase Types" \
            + "Queda bastante feo, usar el campo type para algo mejor.")



debugTODO("pyPEG tiene problemas con la primera y ultima lineas de el " + \
         "archivo de entrada :S, es como que no las detecta en .line")



debugTODO("Module contextvars and synchroacts quizas deberian poseer " + \
          "clase propia y no ser parseadas en Module.")



debugTODO("Cambiar los printMe() por __string__ o __unicode__.")



debugTODO("Chequeo exahustivo usando input bien grande y abarcativo.")



debugTODO("Clase Types y todo lo que hago con ella esta al reverendo pedo.")



debugTODO("Comprobar redaccion y ortografia con algun traductor :s")



debugTODO("Podria usar MATHFORM en vez de INT para los RANGE. Lo mismo " \
        + "pasa en otro lados.")



debugURGENT("Usar CTL en vez de LTL ya que es mucho mas rapido de chequear")



debugTODO("Revisar todo este modulo, packrat por se clava con la ltlspec"  \
           + " G ( just(w) -> X ((just(r) -> X (sys.value = sys.output)) " \
           + "U just(w))).")



debugTODO("Definir todo esto de nuevo, si o si primero en hoja :S")



debugTODO("Lograr trazas de contraejemplo mas cortas y lindas :D")



debugURGENT("lo que dice aca abajo")
"""
    Notar que en la regla de NEXTASIGN, IDENT nunca va a matchear porque 
    PROPFORM contiene a los matches de IDENT, y por lo tanto matchea antes. Sin 
    embargo no quiere decir que el valor devuelto sea un formula proposicional 
    (puede ser por ejemplo una variable que represente un valor entero y no un 
    booleano).
    Me parece que es un error en lo que estoy definiendo. No deberia definir
    las cosas en base a significados semanticos como "formula proposional porque
    es un valor booleano". Sin embargo hacerlo ayuda muchisimo a no tener que
    revisar todo mas adelante.
"""



debugTODO( "Mejorar el manejo de Excepciones :S colocar mas campos con valores"\
         + " y menos mensajes de error :D")




