from rpython.rlib.objectmodel import specialize, not_rpython


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

    def copy(self, mach):
        args = []
        for arg in self.args:
            args.append(arg.copy(mach))
        return Compound(self.fsym, args)

    def occurs(self, t):
        for arg in self.args:
            if arg.occurs(t):
                return True
        return False

    def same(self, t):
        return t.same_compound(self)

    def same_compound(self, t):
        if not self.fsym is t.fsym:
            return False
        for i in range(self.fsym.arity):
            if not self.args[i].same(t.args[i]):
                return False
        return True

    def unify(self, mach, t):
        return t.unify_compound(mach, self)

    def unify_compound(self, mach, t):
        if not self.fsym is t.fsym:
            return False
        for i in range(self.fsym.arity):
            if not self.args[i].unify(mach, t.args[i]):
                return False
        return True

    def unroll(self):
        return self

class Variable(Object):
    def __init__(self, varno):
        self.instance = self
        self.varno = varno

    def stringify(self):
        return "_" + str(self.varno)

    def copy(self, mach):
        if self.instance is self:
            var = mach.new_var()
            mach.bind(self, var)
            return var
        return self.instance.copy(mach)

    def same(self, t):
        if self.instance is self:
            return self is t.unroll()
        return self.instance.same(t)

    def same_compound(self, other):
        return False

    def unify(self, mach, t):
        if self.instance is not self:
            return self.instance.unify(mach, t)
        t = t.unroll()
        if self is t:
            return True
        if t.occurs(self):
            return False
        mach.bind(self, t)
        return True

    def unify_compound(self, mach, t):
        return self.unify(mach, t)

    def unroll(self):
        if self.instance is self:
            return self
        else:
            return self.instance.unroll()
        

known_atoms = {}

@not_rpython
def atom(name, arity):
    key = name, arity
    if key in known_atoms:
        return known_atoms[key]
    atom = Atom(name, arity)
    known_atoms[key] = atom
    return atom

NIL  = atom("nil", 0)
CONS = atom(":", 2)

def as_list(cons):
    result = []
    while True:
        assert isinstance(cons, Compound)
        atom = cons.fsym 
        if cons.fsym is NIL:
            return result
        elif cons.fsym is CONS:
            result.append(cons.args[0])
            cons = cons.args[1]
        else:
            raise ValueError("internal function as_list received non-list")

# Any mutation to any data structure must be
# recorded in the trail.
class Trail:
    def __init__(self, next_varno):
        self.sofar = []
        self.next_varno = next_varno

    def note(self):
        return len(self.sofar)

    def push(self, action):
        self.sofar.append(action)

    def undo(self, whereto):
        while len(self.sofar) != whereto:
            self.sofar.pop().reset()

    def new_var(self):
        var = Variable(self.next_varno)
        self.next_varno += 1
        return var

    def variant(self, obj):
        t = self.note()
        ret = obj.copy(self)
        self.undo(t)
        return ret

    def bind(self, this, value):
        this.instance = value
        self.push(Bound(this))

class Action(object):
    pass

class Bound(Action):
    def __init__(self, this):
        self.this = this

    def reset(self):
        self.this.instance = self.this
