from objects import Atom, Compound, Integer, Variable
from objects import known_atoms, atom, as_list, wrap
from objects import CONS, NIL, AND, OR, TRUE, FALSE, failure, success
from objects import Trail
import os

CLAUSE = atom("<-", 2)
SAME = atom("same", 2)
UNIFY = atom("=", 2)
COND2 = atom("cond", 2)
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

    def solve(self, cb, goal, next_varno):
        conj = goal
        disj = []
        mach = Trail(conj, disj, next_varno)
        return solve(mach, self, cb)

WRITE = atom("write", 1)
EXIT = atom("exit", 1)

CHR_ADD_CONSTRAINT = atom("chr_add_constraint", 2)
CHR_ALIVE = atom("chr_alive", 1)
CHR_PARTNER = atom("chr_partner", 3)
CHR_ACTIVATE = atom("chr_activate", 1)
CHR_SUSPEND1 = atom("chr_suspend", 1)
CHR_SUSPEND2 = atom("chr_suspend", 2)
CHR_KILL     = atom("chr_kill", 1)
CHR_PRINTOUT = atom("chr_printout", 0)

def solve(mach, program, cb, debug=False):
    goal = mach.next_goal(cb)
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
            left = goal.args[0]
            right = goal.args[1]
            if not mach.unify(left, right):
                mach.conj = failure
        elif goal.fsym is COND2:
            mach.backtrack += 1
            t = mach.note()
            csucc = CondSuccess()
            cgoal = goal.args[0]
            cconj = goal.args[1]
            conj = mach.conj
            disj = mach.disj
            mach.conj = cgoal
            mach.disj = []
            solve(mach, program, csucc, debug)
            mach.conj = conj
            mach.disj = disj
            mach.backtrack -= 1
            if csucc.success:
                mach.invoke(cconj)
            else:
                mach.undo(t)
        elif goal.fsym is CHR_ADD_CONSTRAINT:
            c = goal.args[0]
            assert isinstance(c, Compound)
            chrid = mach.next_chrid
            mach.next_chrid += 1
            mach.chr_add_constraint(chrid, c)
            if not mach.unify(goal.args[1], wrap(chrid)):
                mach.conj = failure
        elif goal.fsym is CHR_ALIVE:
            a = goal.args[0].unroll()
            assert isinstance(a, Integer)
            if a.bignum.toint() not in mach.chr_by_id:
                mach.conj = failure
        elif goal.fsym is CHR_PARTNER:
            pattern    = goal.args[0].unroll()
            assert isinstance(pattern, Compound)
            pattern_id = goal.args[1]
            occur      = goal.args[2].unroll()
            assert isinstance(occur, Integer)
            occur = occur.bignum.toint()
            patterns = mach.chr_by_fsym.get(pattern.fsym, {})
            found = False
            this = 0
            for chrid in patterns:
                if occur in mach.chr_history.get(chrid, {}):
                    continue
                if this is not None:
                    mach.choicepoint([
                        Compound(UNIFY, [pattern, mach.chr_by_id[chrid]]),
                        Compound(UNIFY, [pattern_id, wrap(chrid)]),
                        Compound(CHR_ACTIVATE, [wrap(chrid)])])
                else:
                    found = True
                    this = chrid
            if found:
                mach.expand([
                    Compound(UNIFY, [pattern, mach.chr_by_id[this]]),
                    Compound(UNIFY, [pattern_id, wrap(this)]),
                    Compound(CHR_ACTIVATE, [wrap(this)])])
            else:
                mach.conj = failure
        elif goal.fsym is CHR_ACTIVATE:
            pattern_id = goal.args[0].unroll()
            assert isinstance(pattern_id, Integer)
            mach.chr_activate(pattern_id.bignum.toint())
        elif goal.fsym is CHR_SUSPEND1:
            pattern_id = goal.args[0].unroll()
            assert isinstance(pattern_id, Integer)
            mach.chr_suspend(pattern_id.bignum.toint())
        elif goal.fsym is CHR_SUSPEND2:
            pattern_id = goal.args[0].unroll()
            assert isinstance(pattern_id, Integer)
            pattern_id = pattern_id.bignum.toint()
            occur      = goal.args[1].unroll()
            assert isinstance(occur, Integer)
            occur = occur.bignum.toint()
            mach.chr_suspend_2(pattern_id, occur)
        elif goal.fsym is CHR_KILL:
            pattern_id = goal.args[0].unroll()
            assert isinstance(pattern_id, Integer)
            mach.chr_kill(pattern_id.bignum.toint())
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
        # Implementation of side effects in logic language
        # are bit of a question.
        # This looks like slightly wrong way to do it.
        elif goal.fsym is EXIT:
            a = goal.args[0].unroll()
            if isinstance(a, Integer):
                raise Exiting(a.bignum.toint())
            else:
                mach.conj = failure
        elif goal.fsym is WRITE:
            s = goal.args[0].stringify()
            os.write(1, s + "\n")
        elif goal.fsym is CHR_PRINTOUT:
            for chrid, const in mach.chr_by_id.iteritems():
                s = const.stringify()
                os.write(1, "chr%d: %s\n" % (chrid, s))
        else:
            raise ValueError("unknown predicate: %s" % goal.stringify())
        if debug:
            print "=> " + mach.conj.stringify()
        goal = mach.next_goal(cb)

class Success(object):
    def signal(self, mach):
        return False

class CondSuccess(Success):
    def __init__(self):
        self.success = False

    def signal(self, mach):
        self.success = True
        return True

class Exiting(Exception):
    def __init__(self, status):
        self.status = status
