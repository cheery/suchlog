from objects import Atom, Compound, Variable, known_atoms, atom, as_list
from objects import CONS, NIL, AND, OR, TRUE, FALSE, failure, success
from objects import Trail

CLAUSE = atom("<-", 2)
SAME = atom("same", 2)
UNIFY = atom("=", 2)
DEF = atom("DEF", 2)

def load(code):
    defs = {}
    for clause in reversed(as_list(code)):
        assert isinstance(clause, Compound)
        if clause.fsym is CLAUSE:
            head = clause.args[0]
            assert isinstance(head, Compound)
            if head.fsym in defs:
                rest = defs[head.fsym]
            else:
                rest = Compound(NIL, [])
            defs[head.fsym] = Compound(CONS, [clause, rest])
        else:
            raise ValueError("machine.load received a non-program")
    return Program(defs)

class Program:
    def __init__(self, defs):
        self.defs = defs

    def solve(self, success, goal, next_varno):
        conj = goal
        disj = []
        mach = Trail(success, conj, disj, next_varno)
        return solve(mach, self)

def solve(mach, program, debug=False):
    goal = mach.next_goal()
    while goal is not None:
        if debug:
            print
            for _, a in mach.disj:
                print "   " + a.stringify()
            print "** " + goal.stringify() + "#" + mach.conj.stringify()
        if goal.fsym is TRUE:
            pass
        elif goal.fsym is FALSE:
            mach.conj = failure
        elif goal.fsym is AND:
            car = goal.args[0]
            cdr = goal.args[1]
            mach.expand([car, cdr])
        elif goal.fsym is OR:
            car = goal.args[0]
            cdr = goal.args[1]
            mach.choicepoint([cdr])
            mach.invoke(car)
        elif goal.fsym is SAME:
            car = goal.args[0]
            cdr = goal.args[1]
            if not car.same(cdr):
                mach.conj = failure
        elif goal.fsym is UNIFY:
            car = goal.args[0]
            cdr = goal.args[1]
            if not car.unify(mach, cdr):
                mach.conj = failure
        elif goal.fsym is DEF:
            head = goal.args[0]
            clause = goal.args[1]
            assert clause.fsym is CONS
            assert clause.args[0].fsym is CLAUSE
            top = mach.variant(clause.args[0])
            nxt = clause.args[1]
            if nxt.fsym is not NIL:
                mach.choicepoint([Compound(DEF, [head, nxt])])
            mach.expand([Compound(UNIFY, [head, top.args[0]]), top.args[1]])
        elif goal.fsym in program.defs:
            clauses = program.defs[goal.fsym]
            mach.invoke(Compound(DEF, [goal, clauses]))
        else:
            raise ValueError("unknown predicate: %s" % goal.stringify())
        if debug:
            print "=> " + mach.conj.stringify()
        goal = mach.next_goal()
