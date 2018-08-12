class Object:
    pass

class Atom:
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def __repr__(self):
        return "{}".format(self.name, self.arity)

class Compound(Object):
    def __init__(self, fsym, args):
        self.fsym = fsym
        self.args = args
        assert fsym.arity == len(args)

    def stringify(self):
        out = [self.fsym.name]
        if len(self.args) == 0:
            return "".join(out)
        out.append("(")
        sp = ""
        for arg in self.args:
            out.append(sp)
            out.append(arg.stringify())
            sp = ", "
        out.append(")")
        return "".join(out)

class Variable(Object):
    def __init__(self, varno):
        self.instance = self
        self.varno = varno

    def stringify(self):
        return "_" + str(self.varno)

def as_list(cons):
    assert isinstance(cons, Compound)
    result = []
    while True:
        atom = cons.fsym 
        if atom.name == "nil" and atom.arity == 0:
            return result
        elif atom.name == ":" and atom.arity == 2:
            result.append(cons.args[0])
            cons = cons.args[1]
        else:
            raise ValueError("internal function as_list received non-list")
