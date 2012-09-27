import sys, os, fileinput
#sys.path.append(os.path.abspath('../'))

from pyPEG import parse
from GrammarRules import GRAMMAR, COMMENT, SIMPLEXPR



"""~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"""


if __name__ == "__main__":

    _file = fileinput.input()
    _ast  = parse(SIMPLEXPR, _file, True, COMMENT)
    print _ast






