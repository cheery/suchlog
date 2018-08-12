from objects import Atom, Compound, Variable, atom
from rpython.rlib import rfile
import machine
import parser
import os

def new_entry_point(config):
    return main

MAIN = atom("main", 0)

def main(argv):
    if len(argv) <= 1:
        return 1

    fd = rfile.create_file(argv[1], 'rb')
    try:
        source = fd.read()
    finally:
        fd.close()

    code, next_varno = parser.parse(source)
    program = machine.load(code)
    program.solve(succ, Compound(MAIN, []), next_varno)
    return 0

def succ():
    print "wow!"
