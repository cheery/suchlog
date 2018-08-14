from objects import Atom, Compound, Integer, Variable
from objects import known_atoms, atom, as_list, wrap
from objects import CONS, NIL, AND, OR, TRUE, FALSE, failure, success
from objects import Trail
import os

CLAUSE = atom("<-", 2)
CONSTRAINT_RULE = atom("constraint_rule", 5)

SAME = atom("same", 2)
UNIFY = atom("=", 2)
COND2 = atom("cond", 2)
DEF = atom("DEF", 2)

def load(code, varno=100):
    defs = {}
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
            # Add every free variable that appears between keep/drop/guard and goal
            # Add free variable for every ID
            # into goal: prepend chr_kill for 'drops'
            #            prepend chr_suspend(X, OCU) for 'keeps'
            name = clause.args[0]
            assert isinstance(name, Compound)
            name = name.fsym.name
            keep = as_list(clause.args[1])
            drop = as_list(clause.args[2])
            guard = clause.args[3]
            goal = clause.args[4]
            a = find_free(keep + drop + [guard])
            b = find_free([goal])
            heads = []
            a_args = []
            v_args = []
            for k in keep:
                ID_THIS = Variable(varno)
                OCU_THIS = occurrenceno
                varno += 1
                occurrenceno += 1
                heads.append((ID_THIS, OCU_THIS, k))
                goal = Compound(AND, [
                    Compound(CHR_SUSPEND2, [ID_THIS, wrap(OCU_THIS)]),
                    goal])
                a_args.append(ID_THIS)
            for d in drop:
                ID_THIS = Variable(varno)
                OCU_THIS = occurrenceno
                varno += 1
                occurrenceno += 1
                heads.append((ID_THIS, OCU_THIS, k))
                goal = Compound(AND, [
                    Compound(CHR_KILL, [ID_THIS]),
                    goal])
                a_args.append(ID_THIS)
            for v in b:
                if v not in a:
                    continue
                a_args.append(v)
                v_args.append(v)
            # Create new hidden fsym with 'name.apply'
            fapp = Atom(name + ".apply", len(a_args))
            assert fapp not in defs
            defs[fapp] = Compound(CONS, [
                Compound(CLAUSE, [
                    Compound(fapp, list(a_args)),
                    goal]),
                Compound(NIL, [])])
            print defs[fapp].stringify()

            j = 0
            for this_id, ocu_this, k in heads:
                fconstr = k.fsym
                ccond   = guard
                for that_id, that_ocu, hed in heads:
                    if that_id is this_id:
                        continue
                    ccond = Compound(AND, [
                        Compound(CHR_PARTNER, [hed, that_id, wrap(that_ocu)]),
                        ccond])
                # name cond by occurrence: 'name.N'
                fccond = Atom(name + ".%d" % ocu_this, len(a_args) + fconstr.arity)
                assert fccond not in defs
                # Need to insert k.fsym.arity
                # variables to front of a_args.
                defs[fccond] = Compound(CONS, [
                    Compound(CLAUSE, [Compound(fccond, k.args + a_args), ccond]),
                    Compound(NIL, [])])
                print defs[fccond].stringify()
                try:
                    constraints[fconstr].append((fccond, fapp, j))
                except KeyError as _:
                    constraints[fconstr] = [(fccond, fapp, j)]
                j += 1

        else:
            raise ValueError("machine.load received a non-program")

    # For every constraint...
    for fconstr, occurs in constraints.iteritems():
        k_args = []
        for _ in range(fconstr.arity):
            k_args.append(Variable(varno))
            varno += 1
        this_id = Variable(varno)
        varno += 1
        goal = Compound(CHR_SUSPEND1, [this_id])

        for fccond, fapp, j in occurs:
            a_args = []
            for i in range(fapp.arity):
                if i == j:
                    a_args.append(this_id)
                else:
                    a_args.append(Variable(varno))
                    varno += 1
            c2 = Compound(COND2, [
                Compound(AND, [
                    Compound(CHR_ALIVE, [this_id]),
                    Compound(fccond, k_args + a_args)
                ]),
                Compound(fapp, list(a_args))])
            goal = Compound(AND, [c2, goal])
        # finalize the goal with chr_add_constraint(head(X...), ID)
        head = Compound(fconstr, k_args)
        goal = Compound(AND, [
            Compound(CHR_ADD_CONSTRAINT, [
                head,
                this_id]), goal])

        defs[fconstr] = Compound(CONS, [
            Compound(CLAUSE, [head, goal]),
            Compound(NIL, [])])
        print defs[fconstr].stringify()

    return Program(defs)

# Find every free occurrence of variables in the list of items.
def find_free(items):
    free = {}
    for item in items:
        find_free_(item.unroll(), free)
    return free

def find_free_(item, free):
    if isinstance(item, Variable):
        free[item] = None
    elif isinstance(item, Compound):
        for a in item.args:
            find_free_(a.unroll(), free)

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
