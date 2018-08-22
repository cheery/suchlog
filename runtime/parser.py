from rply import Token, LexerGenerator, ParserGenerator
from rply.token import BaseBox
from objects import Atom, Compound, Variable, known_atoms, atom, as_list
from objects import parse_integer

leg = LexerGenerator()
leg.ignore(r'#.*\n')
leg.ignore(r'\s+')
leg.add('ATOM',         r'[a-z][a-zA-Z0-9_]*')
leg.add('VARIABLE',     r'[A-Z_][a-zA-Z0-9_]*')
leg.add('INTEGER',      r'[0-9]+')
leg.add('IMPLICATION',  r"<-")
leg.add('LEFTPAREN',    r"\(")
leg.add('RIGHTPAREN',   r"\)")
leg.add('LEFTBRACKET',  r"\[")
leg.add('RIGHTBRACKET', r"\]")
leg.add('COMMA',        r",")
leg.add('AT',           r"@")
leg.add('VBAR',         r"\|")
leg.add('SIMP',         r"<=>")
leg.add('PROP',         r"==>")
leg.add('UNIFY',        r"=")
leg.add('COLON',        r":")
leg.add('SEMICOLON',    r";")
lexer = leg.build()

pg = ParserGenerator(
    ['ATOM', 'VARIABLE', 'IMPLICATION',
     'UNIFY', 'LEFTPAREN', 'RIGHTPAREN',
     'LEFTBRACKET', 'RIGHTBRACKET', 'COLON',
     'INTEGER',
     'AT', 'VBAR', 'SIMP', 'PROP', 'SEMICOLON',
     'LEFTPAREN0', 'COMMA', 'LINE'])

@pg.production('file : ')
def file_blank(env, p):
    return Box(env.getnil())

@pg.production('file : clause')
def file_clause(env, p):
    car = unbox(p[0])
    cdr = env.getnil()
    return Box(env.getcons(car, cdr))

@pg.production('file : clause LINE file')
def file_clause(env, p):
    car = unbox(p[0])
    cdr = unbox(p[2])
    return Box(env.getcons(car, cdr))

@pg.production('goal : formula')
def goal_formula(env, p):
    return p[0]

@pg.production('goal : formula goal')
def goal_formula(env, p):
    a = unbox(p[0])
    b = unbox(p[1])
    return Box(Compound(env.getatom('and', 2), [a, b]))

@pg.production('clause : ATOM AT predicate_list guard SIMP goal')
def clause_simplification(env, p):
    name = Compound(env.getatom(p[0].getstr(), 0), [])
    keep = env.getnil()
    drop = unbox(p[2])
    guard = unbox(p[3])
    goal = unbox(p[5])
    return Box(Compound(env.getatom('constraint_rule', 5),
        [name, keep, drop, guard, goal]))

@pg.production('clause : ATOM AT predicate_list guard PROP goal')
def clause_propagation(env, p):
    name = Compound(env.getatom(p[0].getstr(), 0), [])
    keep = unbox(p[2])
    drop = env.getnil()
    guard = unbox(p[3])
    goal = unbox(p[5])
    return Box(Compound(env.getatom('constraint_rule', 5),
        [name, keep, drop, guard, goal]))

@pg.production('clause : ATOM AT predicate_list SEMICOLON predicate_list guard SIMP goal')
def clause_simpagation(env, p):
    name = Compound(env.getatom(p[0].getstr(), 0), [])
    keep = unbox(p[2])
    drop = unbox(p[4])
    guard = unbox(p[5])
    goal = unbox(p[7])
    return Box(Compound(env.getatom('constraint_rule', 5),
        [name, keep, drop, guard, goal]))

@pg.production('guard : ')
def empty_guard(env, p):
    return Box(Compound(env.getatom('true', 0), []))

@pg.production('guard : VBAR formula')
def empty_guard(env, p):
    return p[1]

@pg.production('clause : formula')
def clause_axiom(env, p):
    head = unbox(p[0])
    body = Compound(env.getatom('true', 0), [])
    return Box(Compound(env.getatom('<-', 2), [head, body]))

@pg.production('clause : formula IMPLICATION goal ')
def clause_rule(env, p):
    head = unbox(p[0])
    body = unbox(p[2])
    return Box(Compound(env.getatom('<-', 2), [head, body]))

@pg.production('predicate : predicate20')
def predicate_passthrough(env, p):
    return p[0]

@pg.production('predicate : predicate20 COLON predicate')
def predicate_list(env, p):
    car = unbox(p[0])
    cdr = unbox(p[2])
    return Box(env.getcons(car, cdr))

@pg.production('predicate_list : predicate')
def predicate_list_first(env, p):
    car = unbox(p[0])
    cdr = env.getnil()
    return Box(env.getcons(car, cdr))

@pg.production('predicate_list : predicate COMMA predicate_list')
def predicate_list_next(env, p):
    car = unbox(p[0])
    cdr = unbox(p[2])
    return Box(env.getcons(car, cdr))

@pg.production('formula     : ATOM')
@pg.production('predicate20 : ATOM')
def predicate_atom(env, p):
    return Box(Compound(env.getatom(p[0].getstr(), 0), []))

@pg.production('predicate20 : INTEGER')
def predicate_integer(env, p):
    return Box(parse_integer(p[0].getstr()))

@pg.production('predicate20 : VARIABLE')
def predicate_variable(env, p):
    return Box(env.getvar(p[0].getstr()))

@pg.production('formula   : ATOM LEFTPAREN predicate_list RIGHTPAREN')
@pg.production('predicate20 : ATOM LEFTPAREN predicate_list RIGHTPAREN')
def predicate_compound(env, p):
    seq = as_list(unbox(p[2]))
    atom = env.getatom(p[0].getstr(), len(seq))
    return Box(Compound(atom, seq))

@pg.production('formula : predicate UNIFY predicate')
def formula_unify(env, p):
    left  = unbox(p[0])
    right = unbox(p[2])
    atom = env.getatom("=", 2)
    return Box(Compound(atom, [left, right]))

@pg.production('formula   : LEFTPAREN0 predicate RIGHTPAREN')
@pg.production('predicate20 : LEFTPAREN0 predicate RIGHTPAREN')
def parentheses(env, p):
    return p[1]

@pg.production('predicate20 : LEFTBRACKET list_predicate RIGHTBRACKET')
def predicate_list(env, p):
    return p[1]

@pg.production('list_predicate : ')
def list_empty(env, p):
    return Box(env.getnil())

@pg.production('list_predicate : predicate')
def predicate_list_first(env, p):
    car = unbox(p[0])
    cdr = env.getnil()
    return Box(env.getcons(car, cdr))

@pg.production('list_predicate : predicate COMMA list_predicate')
def predicate_list_next(env, p):
    car = unbox(p[0])
    cdr = unbox(p[2])
    return Box(env.getcons(car, cdr))

@pg.error
def error_handler(env, token):
    raise ValueError("%d: Ran into a %s where it wasn't expected" % 
        (token.source_pos.lineno, token.gettokentype()))

parser = pg.build()

class ParserState(object):
    def __init__(self, next_varno):
        self.atoms = {}
        self.variables = {}
        self.next_varno = next_varno
    
    def getatom(self, name, arity):
        key = (name, arity)
        if key in known_atoms:
            return known_atoms[key]
        try:
            return self.atoms[key]
        except KeyError as _:
            atom = Atom(name, arity)
            self.atoms[key] = atom
            return atom

    def getvar(self, name):
        if name == "_":
            var = Variable(self.next_varno)
            self.next_varno += 1
            return var
        try:
            return self.variables[name]
        except KeyError as _:
            var = Variable(self.next_varno)
            self.variables[name] = var
            self.next_varno += 1
            return var

    def getnil(self):
        return Compound(self.getatom("nil", 0), [])

    def getcons(self, car, cdr):
        return Compound(self.getatom(":", 2), [car, cdr])

def layout(tokens):
    lineno = -1
    precede = ""
    for token in tokens:
        if lineno < 0:
            lineno = token.source_pos.lineno
        if lineno < token.source_pos.lineno:
            lineno = token.source_pos.lineno
            if token.source_pos.colno == 1:
                yield Token("LINE", "")
            precede = ""
        if token.gettokentype() == "LEFTPAREN" and precede != "ATOM":
            yield Token("LEFTPAREN0", token.getstr())
        else:
            yield token
        precede = token.gettokentype()

def parse(source):
    state = ParserState(0)
    code = unbox(parser.parse(layout(lexer.lex(source)), state=state))
    return code, state.next_varno

class Box(BaseBox):
    def __init__(self, value):
        self.value = value

def unbox(box):
    assert isinstance(box, Box)
    return box.value
