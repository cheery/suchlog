from objects import Atom, Compound, Integer, Variable
from objects import known_atoms, atom, as_list, wrap
from objects import CONS, NIL, AND, OR, TRUE, FALSE, failure, success
from objects import Trail, UNIFY_ATTS, BIND_HARD
import os

CLAUSE = atom("<-", 2)
CONSTRAINT_RULE = atom("constraint_rule", 5)

SAME = atom("same", 2)
UNIFY = atom("=", 2)
COND2 = atom("cond", 2)
DEF = atom("DEF", 2)

def load(code, varno=100, debug=False):
    defs = {}
    chrs = []
    constraints = {}
    occurrenceno = 0
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
        elif clause.fsym is CONSTRAINT_RULE:
            name = clause.args[0]
            assert isinstance(name, Compound)
            name = name.fsym.name
            keep = as_list(clause.args[1])
            drop = as_list(clause.args[2])
            guard = clause.args[3]
            goal = clause.args[4]
            this = CHR(name, keep + drop, len(keep), guard, goal)
            chrs.append(this)
            index = 0
            for k in this.pattern:
                assert isinstance(k, Compound)
                if k.fsym in constraints:
                    constraints[k.fsym].insert(0, (this, index))
                else:
                    constraints[k.fsym] = [(this, index)]
                index += 1
        else:
            raise ValueError("machine.load received a non-program")

    return Program(defs, constraints)

class Program:
    def __init__(self, defs, constraints):
        self.defs = defs
        self.constraints = constraints

    def solve(self, cb, goal, next_varno):
        conj = goal
        disj = []
        mach = Trail(conj, disj, next_varno)
        return solve(mach, self, cb)

WRITE = atom("write", 1)
EXIT = atom("exit", 1)

CHR_RESUME   = atom("chr_resume", 2)
CHR_PRINTOUT = atom("chr_printout", 0)

GET_ATTS = atom("get_atts", 2)
PUT_ATTS = atom("put_atts", 2)
LIST_ATTS = atom("list_atts", 2)

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
        # I wonder if this is still required, or if it should be improved.
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
        elif goal.fsym is GET_ATTS:
            var = goal.args[0]
            spec = goal.args[1]
            assert isinstance(spec, Compound)
            val = var.attr.get(spec.fsym, None)
            if val is None:
                mach.conj = failure
            else:
                if not mach.unify(val, spec):
                    mach.conj = failure
        elif goal.fsym is PUT_ATTS:
            var = goal.args[0]
            spec = goal.args[1]
            assert isinstance(spec, Compound)
            mach.put_atts(var, spec.fsym, spec)
        elif goal.fsym is BIND_HARD:
            var = goal.args[0]
            val = goal.args[1]
            if isinstance(var, Variable) and var.instance is var:
                mach.bind_hard(var, val)
            else:
                if not mach.unify(var, val):
                    mach.conj = failure
        elif goal.fsym is LIST_ATTS:
            var = goal.args[0]
            assert isinstance(var, Variable)
            ret = goal.args[1]
            res = Compound(NIL, [])
            for val in var.attr.itervalues():
                res = Compound(CONS, [val, res])
            if not mach.unify(ret, res):
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
            mach.expand([Compound(UNIFY, [head, top.args[0]]),
                #Compound(WRITE, [head]),
                top.args[1]])
        elif goal.fsym in program.defs:
            clauses = program.defs[goal.fsym]
            mach.invoke(Compound(DEF, [goal, clauses]))
        elif goal.fsym in program.constraints:
            chr_add_constraint(goal, mach, program)
        elif goal.fsym is CHR_RESUME:
            chr_resume(goal, mach, program)
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

class CHR:
    def __init__(self, name, pattern, keep, guard, goal):
        self.name = name
        self.pattern = pattern
        self.keep  = keep
        self.guard = guard
        self.goal = goal

# The constraints would be convenient to implement
# if there were "matching without unification"
# Also for checking guards the constraint store
# needs to be locked.
def chr_add_constraint(goal, mach, program):
    assert isinstance(goal, Compound)
    chrid = mach.next_chrid
    mach.next_chrid += 1
    mach.chr_add_constraint(chrid, goal)
    #print 'start resolution:    %d %s' % (chrid, goal.stringify())
    assert not mach.chr_lock
    mach.chr_lock = True
    constraint_resolution(goal.fsym, chrid, mach, program)
    mach.chr_lock = False
    #print 'stopped  resolution: %d' % chrid

def chr_resume(goal, mach, program):
    chrid = goal.args[0]
    assert isinstance(chrid, Integer)
    chrid = chrid.bignum.toint()
    start = goal.args[1]
    assert isinstance(start, Integer)
    start = start.bignum.toint()
    fsym = mach.chr_by_id[chrid].fsym
    #print 'start resolution:    %d' % chrid
    assert not mach.chr_lock
    mach.chr_lock = True
    constraint_resolution(fsym, chrid, mach, program)
    mach.chr_lock = False
    #print 'stopped  resolution: %d' % chrid

def constraint_resolution(fsym, chrid, mach, program, start=0):
    constraints = program.constraints[fsym]
    for rule, pivot in constraints[start:]:
        #print 'checking rule %s:%d' % (rule.name, pivot)
        memo = execute_rule(rule, pivot, chrid, mach, program)
        if memo is not None:
            goal = mach.variant(rule.goal, memo)
            #print 'success: ' + goal.stringify()
            if rule.keep <= pivot: # The constraint did not survive.
                return mach.expand([goal])
            if start+1 >= len(constraints):
                return mach.expand([goal])
            return mach.expand([goal,
                Compound(CHR_RESUME, [wrap(chrid), wrap(start+1)]) ])
        start += 1

def execute_rule(rule, pivot, chrid, mach, program):
    active = {chrid:None}
    vector = []
    kills  = {}
    memo = {}
    if rule.keep <= pivot:
        kills[chrid] = None
    return search_partner(rule, 0, pivot, chrid, mach, program,
        active, vector, kills, memo)

def search_partner(rule, index, pivot, chrid, mach, program,
        active, vector, kills, memo):
    if index >= len(rule.pattern):
        t = mach.note()
        mach.backtrack += 1
        guard = mach.variant(rule.guard, memo)
        csucc = CondSuccess()
        conj = mach.conj
        disj = mach.disj
        mach.conj = guard
        mach.disj = []
        solve(mach, program, csucc)
        mach.conj = conj
        mach.disj = disj
        mach.backtrack -= 1
        if csucc.success:
            if rule.keep == len(rule.pattern):
                if mach.chr_step_history(list(vector)):
                    return None
            for k in kills.iterkeys():
                mach.chr_kill(k)
            return memo
        else:
            mach.undo(t)
            return None
    if index == pivot:
        if not rule.pattern[index].match(mach.chr_by_id[chrid], memo):
            return None
        vector.append(chrid)
        ret = search_partner(rule, index+1, pivot, chrid,
            mach, program, active, vector, kills, memo)
        vector.pop()
        return ret
    slot = rule.pattern[index]
    for i in mach.chr_by_fsym.get(slot.fsym, {}):
        if i in active:
            continue
        memo_ = memo.copy()
        if slot.match(mach.chr_by_id[i], memo_):
            vector.append(i)
            active[i] = None
            if rule.keep <= index:
                kills[i] = None
            memo_ = search_partner(rule, index+1, pivot, chrid,
                mach, program, active, vector, kills, memo_)
            if memo_ is not None:
                return memo_
            active.pop(i)
            vector.pop()
    return None
