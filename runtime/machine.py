from objects import Atom, Compound, Variable, known_atoms, atom, as_list
from objects import CONS, NIL
from objects import Trail

CLAUSE = atom("<-", 2)
AND = atom("and", 2)
OR  = atom("or", 2)
TRUE = atom("true", 0)
FALSE = atom("false", 0)
SAME = atom("same", 2)
UNIFY = atom("=", 2)
DEF = atom("DEF", 2)

def load(code):
    defs = {}
    for clause in as_list(code):
        assert isinstance(clause, Compound)
        if clause.fsym is CLAUSE:
            head = clause.args[0]
            assert isinstance(head, Compound)
            if head.fsym in defs:
                rest = defs[head.fsym]
            else:
                rest = Compound(NIL, [])
            defs[head.fsym] = Compound(AND, [clause, rest])
        else:
            raise ValueError("machine.load received a non-program")
    return Program(defs)

class Program:
    def __init__(self, defs):
        self.defs = defs

    def solve(self, success, goal, next_varno):
        mach = Trail(next_varno)
        conj = Compound(CONS, [goal, Compound(NIL, [])])
        return solve(success, mach, conj, self)

failure = Compound(FALSE, [])
def solve(success, mach, conj, program):
    disj = []
    while conj.fsym is CONS:
        goal = conj.args[0]
        conj = conj.args[1]
        assert isinstance(goal, Compound)
        if goal.fsym is TRUE:
            pass
        elif goal.fsym is FALSE:
            conj = failure
        elif goal.fsym is AND:
            car = goal.args[0]
            cdr = goal.args[1]
            conj = Compound(CONS, [cdr, conj])
            conj = Compound(CONS, [car, conj])
        elif goal.fsym is OR:
            car = goal.args[0]
            cdr = goal.args[1]
            disj.append((mach.note(), Compound(CONS, [cdr, conj])))
            conj = Compound(CONS, [car, conj])
        elif goal.fsym is SAME:
            car = goal.args[0]
            cdr = goal.args[1]
            if not car.same(cdr):
                conj = failure
        elif goal.fsym is UNIFY:
            car = goal.args[0]
            cdr = goal.args[1]
            if not car.unify(mach, cdr):
                conj = failure
        elif goal.fsym is DEF:
            head = goal.args[0]
            clause = goal.args[1]
            assert clause.fsym is AND
            assert clause.args[0].fsym is CLAUSE
            top = mach.variant(clause.args[0])
            nxt = clause.args[1]
            if nxt.fsym is not NIL:
                df = Compound(DEF, [head, nxt])
                disj.append((mach.note(), Compound(CONS, [df, conj])))
            u    = Compound(UNIFY, [head, top.args[0]])
            conj = Compound(CONS, [top.args[1], conj])
            conj = Compound(CONS, [u, conj])
        elif goal.fsym in program.defs:
            clauses = program.defs[goal.fsym]
            a = Compound(DEF, [goal, clauses])
            conj = Compound(CONS, [a, conj])
        else:
            raise ValueError("unknown predicate: %s" % goal.stringify())

        if conj.fsym is NIL:
            if success() == False:
                disj = []
            conj = failure
        if conj.fsym is FALSE:
            if len(disj) > 0:
                t, conj = disj.pop()
                mach.undo(t)
    assert conj.fsym is NIL or conj.fsym is FALSE

