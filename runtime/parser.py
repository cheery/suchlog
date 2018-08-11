from rply import Token, LexerGenerator, ParserGenerator
from objects import Atom, Compound, Variable, Clause
import sys

def main():
    for decl in parse(sys.stdin.read()):
        print decl

leg = LexerGenerator()
leg.ignore(r'\s+')
leg.add('ATOM',         r'[a-z][a-zA-Z0-9_]*')
leg.add('VARIABLE',     r'[A-Z_][a-zA-Z0-9_]*')
leg.add('IMPLICATION',  r"<-")
leg.add('UNIFY',        r"=")
leg.add('LEFTPAREN',    r"\(")
leg.add('RIGHTPAREN',   r"\)")
leg.add('LEFTBRACKET',  r"\[")
leg.add('RIGHTBRACKET', r"\]")
leg.add('COMMA',        r",")
lexer = leg.build()

pg = ParserGenerator(
    ['ATOM', 'VARIABLE', 'IMPLICATION',
     'UNIFY', 'LEFTPAREN', 'RIGHTPAREN',
     'LEFTBRACKET', 'RIGHTBRACKET',
     'LEFTPAREN0', 'COMMA', 'LINE'])

@pg.production('file : ')
@pg.production('file : clause')
def file_clause(env, p):
    return list(p)

@pg.production('file : file LINE clause')
def file_clause(env, p):
    p[0].append(p[2])
    return p[0]

@pg.production('goal : formula')
def goal_formula(env, p):
    return p[0]

@pg.production('goal : formula goal')
def goal_formula(env, p):
    return Compound(env.getatom('and', 2), [p[0], p[1]])

@pg.production('clause : formula')
def clause_axiom(env, p):
    true = env.getatom('true', 0)
    return Clause(p[0], true)

@pg.production('clause : formula IMPLICATION goal ')
def clause_rule(env, p):
    return Clause(p[0], p[2])

@pg.production('predicate_list : predicate')
def predicate_list_first(env, p):
    return [p[0]]

@pg.production('predicate_list : predicate_list COMMA predicate')
def predicate_list_next(env, p):
    return p[0] + [p[2]]

@pg.production('formula   : ATOM')
@pg.production('predicate : ATOM')
def predicate_atom(env, p):
    return env.getatom(p[0].getstr(), 0)

@pg.production('predicate : VARIABLE')
def predicate_variable(env, p):
    return env.getvar(p[0].getstr())

@pg.production('formula   : ATOM LEFTPAREN predicate_list RIGHTPAREN')
@pg.production('predicate : ATOM LEFTPAREN predicate_list RIGHTPAREN')
def predicate_compound(env, p):
    atom = env.getatom(p[0].getstr(), len(p[2]))
    return Compound(atom, p[2])

@pg.production('formula : predicate UNIFY predicate')
def formula_unify(env, p):
    atom = env.getatom("=", 2)
    return Compound(atom, [p[0], p[2]])

@pg.production('formula   : LEFTPAREN0 predicate RIGHTPAREN')
@pg.production('predicate : LEFTPAREN0 predicate RIGHTPAREN')
def parentheses(env, p):
    return p[1]

@pg.production('predicate : LEFTBRACKET list_predicate RIGHTBRACKET')
def predicate_list(env, p):
    return p[1]

@pg.production('list_predicate : ')
def list_empty(env, p):
    return Compound(env.getatom("nil", 0), [])

@pg.production('list_predicate : predicate')
def predicate_list_first(env, p):
    return Compound(env.getatom(".", 2), [p[0], list_empty(env, p)])

@pg.production('list_predicate : predicate COMMA list_predicate')
def predicate_list_next(env, p):
    return Compound(env.getatom(".", 2), [p[0], p[2]])


@pg.error
def error_handler(env, token):
    raise ValueError("Ran into a %s where it wasn't expected" % token.gettokentype())

parser = pg.build()

class ParserState(object):
    def __init__(self, next_varno):
        self.atoms = {}
        self.variables = {}
        self.next_varno = next_varno
    
    def getatom(self, name, arity):
        try:
            return self.atoms[(name, arity)]
        except KeyError as _:
            atom = Atom(name, arity)
            self.atoms[(name, arity)] = atom
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

def layout(tokens):
    lineno = None
    precede = None
    for token in tokens:
        if lineno is None:
            lineno = token.source_pos.lineno
        if lineno < token.source_pos.lineno:
            lineno = token.source_pos.lineno
            if token.source_pos.colno == 1:
                yield Token("LINE", "")
            precede = None
        if token.gettokentype() == "LEFTPAREN" and precede != "ATOM":
            yield Token("LEFTPAREN0", token.getstr())
        else:
            yield token
        precede = token.gettokentype()

def parse(source):
    state = ParserState(0)
    return parser.parse(layout(lexer.lex(source)), state=state)

if __name__=="__main__":
    main()
