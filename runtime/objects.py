from rpython.rlib.objectmodel import specialize, not_rpython
from rpython.rlib.rbigint import rbigint
from rpython.rlib.rstring import NumberStringParser


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

class Integer(Object):
    def __init__(self, bignum):
        self.bignum = bignum

    def stringify(self):
        return self.bignum.format(digits[:10])

    def copy(self, mach):
        return self

    def occurs(self, t):
        return False

    def same(self, t):
        if isinstance(t, Integer):
            return self.bignum.eq(t.bignum)
        return False

    def same_compound(self, other):
        return False

    def unify(self, mach, t):
        if isinstance(t, Integer):
            return self.bignum.eq(t.bignum)
        return t.unify(mach, self)

    def unify_compound(self, mach, t):
        return False

    def unroll(self):
        return self

def parse_integer(string, base=10):
    if base > 36:
        raise ValueError("Not enough digits to base")
    if base < 0:
        raise ValueError("Negative base")
    literal = string
    parser = NumberStringParser(string, literal, base, 'long')
    return Integer(rbigint._from_numberstring_parser(parser))

digits = "0123456789abcdefghijklmnopqrstuvwxyz"

class Variable(Object):
    def __init__(self, varno):
        self.instance = self
        self.varno = varno
        self.goal = None

    def stringify(self):
        if self.instance is self:
            return "_" + str(self.varno)
        return self.instance.stringify()

    # Note that this is not a generic copy operation.
    # Any hidden and instantiated variable should be
    # removed before using this operation.
    def copy(self, mach):
        if self.instance is self:
            var = mach.new_var()
            mach.bind(self, var)
            return var
        return self.instance

    def occurs(self, t):
        if self.instance is self:
            return t is self
        return self.instance.occurs(t)

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
AND = atom("and", 2)
OR  = atom("or", 2)
TRUE = atom("true", 0)
FALSE = atom("false", 0)

success = Compound(TRUE, [])
failure = Compound(FALSE, [])

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

@specialize.argtype(0)
def wrap(a):
    if isinstance(a, bool):
        return success if a else failure
    if isinstance(a, int):
        return Integer(rbigint.fromint(a))
    assert False, ""

# Any mutation to any data structure must be
# recorded in the trail.
class Trail:
    def __init__(self, conj, disj, next_varno):
        self.sofar = []
        self.conj = conj
        self.disj = disj
        self.next_varno = next_varno
        self.backtrack = 0
        self.next_chrid = 0
        self.chr_by_id = {}
        self.chr_by_fsym = {}
        self.chr_history = {}
        self.chr_active = {}

    def next_goal(self, cb):
        assert isinstance(self.conj, Compound)
        if self.conj.fsym is AND:
            goal = self.conj.args[0]
            self.conj = self.conj.args[1]
            return goal
        elif self.conj.fsym is TRUE:
            if cb.signal(self):
                self.disj = []
            else:
                self.conj = failure
                return self.next_goal(cb)
        elif self.conj.fsym is FALSE:
            if len(self.disj) == 0:
                return None
            t, self.conj = self.disj.pop()
            self.undo(t)
            return self.next_goal(cb)
        else:
            goal = self.conj
            self.conj = success
            return goal

    def invoke(self, goal):
        if isinstance(goal, Compound) and goal.fsym is TRUE:
            return
        self.conj = Compound(AND, [goal, self.conj])

    def expand(self, goals):
        for goal in reversed(goals):
            self.invoke(goal)

    def choicepoint(self, goals):
        conj = self.conj
        for goal in reversed(goals):
            conj = Compound(AND, [goal, conj])
        self.disj.append((self.note(), conj))

    def note(self):
        return len(self.sofar)

    def push(self, action):
        # Concluded this might not work properly.
        #if len(self.disj) > 0 or self.backtrack > 0:
        self.sofar.append(action)

    def undo(self, whereto):
        while len(self.sofar) != whereto:
            self.sofar.pop().reset()

    def new_var(self):
        var = Variable(self.next_varno)
        self.next_varno += 1
        return var

    def variant(self, obj):
        self.backtrack += 1
        t = self.note()
        ret = obj.copy(self)
        self.undo(t)
        self.backtrack -= 1
        return ret

    def unify(self, a, b):
        self.backtrack += 1
        t = self.note()
        ret = a.unify(self, b)
        if not ret:
            self.undo(t)
        self.backtrack -= 1
        return ret

    def bind(self, this, value):
        this.instance = value
        self.push(Bound(this))
        if this.goal is not None:
            self.invoke(this.goal)

    def freeze(self, this, goal):
        self.push(Frozen(this, this.goal))
        if this.goal is None:
            this.goal = goal
        else:
            this.goal = Compound(AND, [goal, this.goal])

    def chr_add_constraint(self, chrid, c):
        self.chr_active[chrid] = None
        self.chr_by_id[chrid] = c
        self.chr_history[chrid] = {}
        try:
            self.chr_by_fsym[c.fsym][chrid] = None
        except KeyError as _:
            self.chr_by_fsym[c.fsym] = {chrid:None}
        self.push(AddedConstraint(self, chrid, c.fsym))

    def chr_activate(self, chrid):
        self.chr_active[chrid] = None
        self.push(Activated(self, chrid))

    def chr_suspend(self, chrid):
        if chrid in self.chr_active:
            self.chr_active.pop(chrid)
            self.push(Deactivated(self, chrid))

    def chr_suspend_2(self, chrid, occur):
        self.chr_suspend(chrid)
        self.chr_history[chrid][occur] = None
        self.push(Propagated(self, chrid, occur))

    def chr_kill(self, chrid):
        self.chr_suspend(chrid)
        prop = self.chr_history.pop(chrid)
        cons = self.chr_by_id.pop(chrid)
        self.chr_by_fsym[cons.fsym].pop(chrid)
        self.push(Killed(self, chrid, prop, cons))

class Action(object):
    pass

class Bound(Action):
    def __init__(self, this):
        self.this = this

    def reset(self):
        self.this.instance = self.this

class Frozen(Action):
    def __init__(self, this, previous_goal):
        self.this = this
        self.previous_goal = previous_goal

    def reset(self):
        self.this.goal = self.previous_goal

class AddedConstraint(Action):
    def __init__(self, mach, chrid, fsym):
        self.mach = mach
        self.chrid = chrid
        self.fsym = fsym

    def reset(self):
        self.mach.chr_by_id.pop(self.chrid)
        self.mach.chr_by_fsym[self.fsym].pop(self.chrid)
        self.mach.chr_active.pop(self.chrid)

class Activated(Action):
    def __init__(self, mach, chrid):
        self.mach = mach
        self.chrid = chrid

    def reset(self):
        self.mach.chr_active.pop(self.chrid)

class Deactivated(Action):
    def __init__(self, mach, chrid):
        self.mach = mach
        self.chrid = chrid

    def reset(self):
        self.mach.chr_active[self.chrid] = None

class Propagated(Action):
    def __init__(self, mach, chrid, occur):
        self.mach  = mach
        self.chrid = chrid
        self.occur = occur

    def reset(self):
        self.mach.chr_history[self.chrid].pop(self.occur)

class Killed(Action):
    def __init__(self, mach, chrid, prop, cons):
        self.mach  = mach
        self.chrid = chrid
        self.prop = prop
        self.cons = cons

    def reset(self):
        self.mach.chr_history[self.chrid] = self.prop
        self.mach.chr_by_id[self.chrid] = self.cons
        self.mach.chr_by_fsym[self.cons.fsym][self.chrid] = None
