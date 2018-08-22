from objects import Atom, Compound, Integer, Variable
from objects import known_atoms, atom, as_list, wrap
from objects import CONS, NIL, AND, OR, TRUE, FALSE, failure, success
from objects import Trail, UNIFY_ATTS, BIND_HARD
from objects import DepthFirstSearch, OrderedSearch
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
        state = OrderedSearch(goal, [], cb)
        mach = Trail(state, next_varno)
        return solve(mach, self)

WRITE = atom("write", 1)
EXIT = atom("exit", 1)

CHR_RESUME   = atom("chr_resume", 2)
CHR_PRINTOUT = atom("chr_printout", 0)
CHR_REVISE   = atom("chr_revise", 1)

GET_ATTS = atom("get_atts", 2)
PUT_ATTS = atom("put_atts", 2)
LIST_ATTS = atom("list_atts", 2)

def solve(mach, program, debug=False):
    goal = mach.state.next_goal(mach)
    while goal is not None:
        if debug:
            print
            for _, a in mach.state.disj:
                print "   " + a.stringify()
            print "** " + goal.stringify() + "#" + mach.state.conj.stringify()
        if goal.fsym is TRUE:
            pass
        elif goal.fsym is FALSE:
            mach.state.fail()
        elif goal.fsym is AND:
            car = goal.args[0]
            cdr = goal.args[1]
            mach.state.expand([car, cdr])
        elif goal.fsym is OR:
            car = goal.args[0]
            cdr = goal.args[1]
            mach.state.choicepoint(mach, [cdr])
            mach.state.invoke(car)
        elif goal.fsym is SAME:
            car = goal.args[0]
            cdr = goal.args[1]
            if not car.same(cdr):
                mach.state.fail()
        elif goal.fsym is UNIFY:
            left = goal.args[0]
            right = goal.args[1]
            if not mach.unify(left, right):
                mach.state.fail()
        # I wonder if this is still required, or if it should be improved.
        elif goal.fsym is COND2:
            mach.backtrack += 1
            t = mach.note()
            csucc = CondSuccess()
            cgoal = goal.args[0]
            cconj = goal.args[1]
            this_state = mach.state
            mach.state = mach.state.subgoal(cgoal, [], csucc)
            solve(mach, program, debug)
            mach.state = this_state
            mach.backtrack -= 1
            if csucc.success:
                mach.state.invoke(cconj)
            else:
                mach.undo(t)
        elif goal.fsym is GET_ATTS:
            var = goal.args[0]
            spec = goal.args[1]
            assert isinstance(spec, Compound)
            val = var.attr.get(spec.fsym, None)
            if val is None:
                mach.state.fail()
            else:
                if not mach.unify(val, spec):
                    mach.state.fail()
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
                    mach.state.fail()
        elif goal.fsym is LIST_ATTS:
            var = goal.args[0]
            assert isinstance(var, Variable)
            ret = goal.args[1]
            res = Compound(NIL, [])
            for val in var.attr.itervalues():
                res = Compound(CONS, [val, res])
            if not mach.unify(ret, res):
                mach.state.fail()
        elif goal.fsym is DEF:
            head = goal.args[0]
            clause = goal.args[1]
            assert clause.fsym is CONS
            assert clause.args[0].fsym is CLAUSE
            top = mach.variant(clause.args[0])
            nxt = clause.args[1]
            if nxt.fsym is not NIL:
                mach.state.choicepoint(mach, [Compound(DEF, [head, nxt])])
            mach.state.expand([Compound(UNIFY, [head, top.args[0]]),
                #Compound(WRITE, [head]),
                top.args[1]])
        elif goal.fsym in program.defs:
            clauses = program.defs[goal.fsym]
            mach.state.invoke(Compound(DEF, [goal, clauses]))
        elif goal.fsym in program.constraints:
            chr_add_constraint(goal, mach, program)
        elif goal.fsym is CHR_RESUME:
            chrid = goal.args[0]
            assert isinstance(chrid, Integer)
            chrid = chrid.bignum.toint()
            start = goal.args[1]
            assert isinstance(start, Integer)
            start = start.bignum.toint()
            chr_resume(chrid, start, mach, program)
        # Implementation of side effects in logic language
        # are bit of a question.
        # This looks like slightly wrong way to do it.
        elif goal.fsym is EXIT:
            a = goal.args[0].unroll()
            if is_ground(a):
                if isinstance(a, Integer):
                    raise Exiting(a.bignum.toint())
                else:
                    mach.state.fail()
            elif mach.chr_lock:
                mach.state.fail()
            else:
                chr_add_constraint(goal, mach, program)
        elif goal.fsym is WRITE:
            a = goal.args[0].unroll()
            if is_ground(a):
                s = a.stringify()
                os.write(1, s + "\n")
            elif mach.chr_lock:
                mach.state.fail()
            else:
                chr_add_constraint(goal, mach, program)
        elif goal.fsym is CHR_REVISE:
            revise = goal
            a = goal.args[0]
            assert isinstance(a, Integer)
            i = a.bignum.toint()
            goal = mach.chr_by_id.get(i, None)
            if goal is not None:
                assert isinstance(goal, Compound)
                if goal.fsym is WRITE and is_ground(goal.args[0]):
                    s = goal.args[0].stringify()
                    os.write(1, s + "\n")
                elif goal.fsym is EXIT and is_ground(goal.args[0]):
                    if isinstance(a, Integer):
                        raise Exiting(a.bignum.toint())
                    else:
                        mach.state.fail()
                else:
                    deep_freeze(mach, goal, revise, True)
                    chr_resume(i, 0, mach, program)
        elif goal.fsym is CHR_PRINTOUT:
            for chrid, const in mach.chr_by_id.iteritems():
                s = const.stringify()
                os.write(1, "chr%d: %s\n" % (chrid, s))
        else:
            raise ValueError("unknown predicate: %s" % goal.stringify())
        if debug:
            print "=> " + mach.state.conj.stringify()
        goal = mach.state.next_goal(mach)

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

# TODO: Note that the constraint propagation doesn't exhaustively
# try every combination there is. I'll probably add it in later.
# TODO: When a constraint is added where there are free variables,
#       the variables should freeze-in an element that re-activates
#       a constraint. I'll probably add this later as well.
def chr_add_constraint(goal, mach, program):
    assert isinstance(goal, Compound)
    chrid = mach.next_chrid
    mach.next_chrid += 1
    mach.chr_add_constraint(chrid, goal)
    deep_freeze(mach, goal, Compound(CHR_REVISE, [wrap(chrid)]))
    #print 'start resolution:    %d %s' % (chrid, goal.stringify())
    # Without locking the database, we'd lose track
    # of constraints added and removed and
    # the constraint resolution step would fail.
    assert not mach.chr_lock
    mach.chr_lock = True
    constraint_resolution(goal.fsym, chrid, mach, program)
    mach.chr_lock = False
    #print 'stopped  resolution: %d' % chrid

def is_ground(val):
    val = val.unroll()
    if isinstance(val, Compound):
        for arg in val.args:
            if not is_ground(arg):
                return False
        return True
    return not isinstance(val, Variable)

def deep_freeze(mach, val, goal, may_occur=False):
    val = val.unroll()
    if isinstance(val, Compound):
        for arg in val.args:
            deep_freeze(mach, arg, goal, may_occur)
    elif isinstance(val, Variable):
        mach.freeze(val, goal, occurs_check=may_occur)

def chr_resume(chrid, start, mach, program):
    fsym = mach.chr_by_id[chrid].fsym
    #print 'start resolution:    %d' % chrid
    assert not mach.chr_lock
    mach.chr_lock = True
    constraint_resolution(fsym, chrid, mach, program)
    mach.chr_lock = False
    #print 'stopped  resolution: %d' % chrid

def constraint_resolution(fsym, chrid, mach, program, start=0):
    constraints = program.constraints.get(fsym, [])
    for rule, pivot in constraints[start:]:
        #print 'checking rule %s:%d' % (rule.name, pivot)
        memo = execute_rule(rule, pivot, chrid, mach, program)
        if memo is not None:
            goal = mach.variant(rule.goal, memo)
            #print 'success: ' + goal.stringify()
            if rule.keep <= pivot: # The constraint did not survive.
                return mach.state.expand([goal])
            if start+1 >= len(constraints):
                return mach.state.expand([goal])
            return mach.state.expand([goal,
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
        this_state = mach.state
        mach.state = mach.state.subgoal(guard, [], csucc)
        solve(mach, program)
        mach.state = this_state
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
