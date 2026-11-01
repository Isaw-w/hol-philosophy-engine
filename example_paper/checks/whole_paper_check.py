"""Check the paragraph HOL of the whole paper at once: are all axioms jointly consistent, and do the
main conclusions follow from them? Usage: python3 whole_paper_check.py PROSE_DIR"""
import re, sys
from pathlib import Path
import z3

Person = z3.DeclareSort("person")
consts = {}


def const(name, typ):
    if name in consts:
        return consts[name]
    if typ == ":person":
        c = z3.Const(name, Person)
    elif typ == ":bool":
        c = z3.Bool(name)
    else:
        c = z3.Function(name, Person, z3.BoolSort())
    consts[name] = c
    return c


TOK = re.compile(r"\s*(<=>|==>|/\\|\\/|~|\(|\)|!|\.|[A-Za-z_][A-Za-z0-9_]*)")


def parse(s, env):
    toks = TOK.findall(s)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def take(t=None):
        tok = toks[pos[0]]
        assert t is None or tok == t, (t, tok, s)
        pos[0] += 1
        return tok

    def binop(next_, op, mk, right=True):
        def f():
            left = next_()
            if peek() == op:
                take(op)
                return mk(left, f())
            return left
        return f

    def atom():
        t = peek()
        if t == "~":
            take()
            return z3.Not(atom())
        if t == "(":
            take("(")
            e = iff()
            take(")")
            return e
        if t == "!":
            take("!")
            v = take()
            take(".")
            x = z3.Const(v, Person)
            saved = env.get(v)
            env[v] = x
            body = iff()          # the binder's scope runs as far right as possible, up to a closing bracket
            if saved is None:
                del env[v]
            else:
                env[v] = saved
            return z3.ForAll([x], body)
        name = take()
        if name in env:
            return env[name]
        c = consts[name]
        if isinstance(c, z3.FuncDeclRef):
            arg = take()
            return c(env.get(arg, consts.get(arg)))
        return c

    conj = binop(atom, "/\\", lambda a, b: z3.And(a, b))
    disj = binop(conj, "\\/", lambda a, b: z3.Or(a, b))
    imp = binop(disj, "==>", lambda a, b: z3.Implies(a, b))
    iff = binop(imp, "<=>", lambda a, b: a == b)
    return iff()


axioms = {}
for src in sorted(Path(sys.argv[1]).glob("s*/p*/source.sml")):
    text = src.read_text()
    for name, typ in re.findall(r'new_constant \("(\w+)", ``(.*?)``\)', text):
        const(name, typ)
    for name, term in re.findall(r'new_axiom \("(\w+)", ``(.*?)``\)', text, re.S):
        axioms[name] = parse(term, {})

s = z3.Solver()
s.set(unsat_core=True)
for name, f in axioms.items():
    s.assert_and_track(f, name)
r = s.check()
print("all axioms of the paper together:", "consistent" if r == z3.sat else "INCONSISTENT")
if r == z3.unsat:
    print("unsat core:", sorted(str(c) for c in s.unsat_core()))
else:
    # neutrality: each formula given on the command line must be both satisfiable and refutable with the paper
    for f in sys.argv[2:]:
        phi = parse(f, {})
        can_hold = s.check(phi) == z3.sat
        can_fail = s.check(z3.Not(phi)) == z3.sat
        print(f"  {f[:70]:70s} can hold: {can_hold}   can fail: {can_fail}")
