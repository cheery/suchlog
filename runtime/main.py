from objects import Atom, Compound, Variable
from rpython.rlib import rfile
import parser
import os

def new_entry_point(config):
    return main

def main(argv):
    if len(argv) <= 1:
        return 1

    fd = rfile.create_file(argv[1], 'rb')
    try:
        source = fd.read()
    finally:
        fd.close()

    decls = parser.parse(source)
    os.write(1, decls.stringify() + "\n")
    return 0
