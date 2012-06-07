import re, fileinput
import sys, os


sys.path.append(os.path.abspath('../'))

from pyPEG import parse
from pyPEG import keyword, _and, _not



def LENG():         return [ (re.compile("!"), VALS, OP, VALS), (re.compile("\!"), VALS)]
def OP():           return re.compile(r"\bU\b")
def VALS():         return re.compile(r"TRUE")
def COMMENT():      return [re.compile(r"//.*"), re.compile("/\*.*?\*/", re.S)]


files = fileinput.input()
result = parse(LENG(), files, True, COMMENT)
print result
