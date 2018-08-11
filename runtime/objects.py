class Object:
    pass

class Atom:
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def __repr__(self):
        return "{}".format(self.name, self.arity)

class Compound(Object):
    def __init__(self, atom, args):
        self.atom = atom
        self.args = args
        assert atom.arity == len(args)

    def __repr__(self):
        if self.atom.arity == 0:
            return repr(self.atom)
        return "{!r}({})".format(self.atom, ", ".join(map(repr, self.args)))

class Variable(Object):
    def __init__(self, varno):
        self.instance = self
        self.varno = varno

    def __repr__(self):
        return "_{}".format(self.varno)

class Clause:
    def __init__(self, head, body):
        self.head = head
        self.body = body

    def __repr__(self):
        return "{!r} <- {!r}".format(self.head, self.body)
