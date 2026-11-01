"""Check a Z3 countermodel in HOL semantics.

Z3 answers questions about a translation of the argument. A "does not follow" rests on a model of that translation,
and the translation can be wrong (an audit, 2026-10-21, and a polymorphic definition read as two symbols, GPT g16_02).
So a countermodel counts only if the original HOL statements, read in an interpretation built from it, come out as
the question needs: the starting points true and the conclusion false. This is what Nitpick does with a potential
counterexample (Blanchette and Nipkow 2010: genuine, potential, likely genuine), and what CEGAR does with an
abstract counterexample (Clarke et al. 2000).

The interpretation: each declared type is the finite universe Z3 gives it; bool, enumerations and finite datatypes are
what they are; num, int, real, lists and recursive datatypes stay infinite. A primitive constant (declared, not
defined) takes its value from the model; one the translation never mentions takes a fixed default, which is a legal
choice since nothing constrains it. A defined constant is evaluated by its own definition, clause by clause, so every
definition holds by construction at whatever type it is used. Values are three-valued, as in Nitpick: a quantifier
over a finite type is enumerated; over an infinite type it is false (for !) or true (for ?) when an instance among
the values met so far settles it, and unknown otherwise. Anything this evaluator does not know is unknown, and an
unknown means the countermodel is not validated, never that it is.

Each HOL term is compiled once into a Python function and then run in every model (Semantics); a model's values and
caches live in an Interp.
"""
import json, time
from fractions import Fraction


class Unknown(Exception):
    pass


def _unknown(why):
    raise Unknown(why)


def is_fun(ty):
    return ty.get("kind") == "type_application" and ty.get("name") == "fun"


def arrow(ty):
    dom = []
    while is_fun(ty):
        dom.append(ty["arguments"][0]); ty = ty["arguments"][1]
    return dom, ty


def strip_comb(t):
    args = []
    while t["kind"] == "application":
        args.append(t["argument"]); t = t["function"]
    return t, list(reversed(args))


def strip_forall(t):
    vs = []
    while True:
        h, a = strip_comb(t)
        if h["kind"] == "constant" and h["name"] == "!" and len(a) == 1 and a[0]["kind"] == "abstraction":
            vs.append(a[0]["variable"]); t = a[0]["body"]
        else:
            return vs, t


def conjuncts(t):
    h, a = strip_comb(t)
    if h["kind"] == "constant" and h["name"] == "/\\" and len(a) == 2:
        return conjuncts(a[0]) + conjuncts(a[1])
    return [t]


def rebuild(h, args):
    for a in args:
        h = {"kind": "application", "function": h, "argument": a}
    return h


def tykey(ty):
    return json.dumps(ty, sort_keys=True)


def match_ty(gen, inst, sub):
    if gen.get("kind") != "type_application":
        k = gen.get("name")
        if k in sub and sub[k] != inst:
            return None
        sub[k] = inst
        return sub
    if inst.get("kind") != "type_application" or gen["name"] != inst["name"] or len(gen["arguments"]) != len(inst["arguments"]):
        return None
    for g, i in zip(gen["arguments"], inst["arguments"]):
        if match_ty(g, i, sub) is None:
            return None
    return sub


def subst_ty(ty, sub):
    if ty.get("kind") != "type_application":
        return sub.get(ty.get("name"), ty)
    return {**ty, "arguments": [subst_ty(a, sub) for a in ty["arguments"]]}


def subst_term(t, sub):
    if not sub:
        return t
    if t["kind"] in ("variable", "constant"):
        return {**t, "type": subst_ty(t["type"], sub)}
    if t["kind"] == "application":
        return {**t, "function": subst_term(t["function"], sub), "argument": subst_term(t["argument"], sub)}
    if t["kind"] == "abstraction":
        return {**t, "variable": subst_term(t["variable"], sub), "body": subst_term(t["body"], sub)}
    return t


def free_vars(t, bound=frozenset()):
    k = t["kind"]
    if k == "variable":
        return set() if t["name"] in bound else {t["name"]}
    if k == "application":
        return free_vars(t["function"], bound) | free_vars(t["argument"], bound)
    if k == "abstraction":
        return free_vars(t["body"], bound | {t["variable"]["name"]})
    return set()


def pattern_vars(p):
    if p["kind"] == "variable":
        return [p["name"]]
    if p["kind"] == "application":
        return pattern_vars(p["function"]) + pattern_vars(p["argument"])
    return []


def definition_clauses(definitions, theory, constructors):
    """(theory, name) -> clauses [(head type, bound variables, argument patterns, right side)] from definition
    theorems: each conjunct !vs. c p1 .. pn = rhs. Datatype constructors are values, never unfolded."""
    out = {}
    for d in definitions:
        outer, whole = strip_forall(d["conclusion"])
        for cj in conjuncts(whole):
            vs, body = strip_forall(cj)
            vs = outer + vs
            h, a = strip_comb(body)
            if not (h["kind"] == "constant" and h["name"] == "=" and len(a) == 2):
                continue
            lh, pats = strip_comb(a[0])
            if lh["kind"] != "constant":
                continue
            if lh.get("theory") == theory and lh["name"] in constructors:
                continue
            out.setdefault((lh.get("theory"), lh["name"]), []).append((lh["type"], vs, pats, a[1]))
    return out


class Other:
    """the values of an infinite type outside the finite set S of values that the model's tables mention (table
    entries, and numbers a table's default compares its argument with) and the argument's numerals. For num and int,
    one Other per gap between consecutive members of S: lo < n < hi (None for no bound). No table entry lies in a
    gap and no comparison with a member of S changes inside one, so one run of a quantifier's body on Other stands
    for every value in its gap. Anything else that would look at the value (arithmetic, a pattern, a Z3
    conversion) is unknown."""
    __slots__ = ("t", "lo", "hi")

    def __init__(self, t, lo=None, hi=None):
        self.t, self.lo, self.hi = t, lo, hi

    def _u(self, *a):
        raise Unknown("an unspecified value looked at")

    def _num(self, k):
        if type(k) is not int:
            raise Unknown("an unspecified value looked at")
        return k

    def __lt__(self, k):                                # every n in the gap < k, none, or unknown
        k = self._num(k)
        if self.hi is not None and self.hi <= k: return True
        if self.lo is not None and self.lo + 1 >= k: return False
        raise Unknown("an unspecified value compared")

    def __le__(self, k):
        k = self._num(k)
        if self.hi is not None and self.hi - 1 <= k: return True
        if self.lo is not None and self.lo + 1 > k: return False
        raise Unknown("an unspecified value compared")

    def __gt__(self, k):
        k = self._num(k)
        if self.lo is not None and self.lo >= k: return True
        if self.hi is not None and self.hi - 1 <= k: return False
        raise Unknown("an unspecified value compared")

    def __ge__(self, k):
        k = self._num(k)
        if self.lo is not None and self.lo + 1 >= k: return True
        if self.hi is not None and self.hi - 1 < k: return False
        raise Unknown("an unspecified value compared")

    def __eq__(self, k):
        if isinstance(k, Other) and k is not self:
            raise Unknown("two unspecified values compared")
        if k is self:
            return True
        k = self._num(k)
        if (self.lo is not None and k <= self.lo) or (self.hi is not None and k >= self.hi): return False
        raise Unknown("an unspecified value compared")

    def __ne__(self, k):
        return not self.__eq__(k)
    __add__ = __radd__ = __sub__ = __rsub__ = __mul__ = __rmul__ = _u
    __floordiv__ = __rfloordiv__ = __mod__ = __rmod__ = __truediv__ = __rtruediv__ = __pow__ = __rpow__ = __neg__ = _u
    __len__ = __getitem__ = __iter__ = __bool__ = _u

    def __hash__(self):
        return id(self)

    def __repr__(self):
        return "<other>"


class DV:
    """a value of a datatype or enumeration: a constructor and its arguments"""
    __slots__ = ("c", "a")

    def __init__(self, c, a):
        self.c, self.a = c, tuple(a)

    def __eq__(self, o):
        if isinstance(o, Other):
            raise Unknown("an unspecified value looked at")
        return isinstance(o, DV) and self.c == o.c and self.a == o.a

    def __hash__(self):
        return hash(("DV", self.c, self.a))

    def __repr__(self):
        return self.c + (repr(self.a) if self.a else "")


class UV:
    """an element of a declared type: one of the things in the universe Z3 gave it"""
    __slots__ = ("t", "k")

    def __init__(self, t, k):
        self.t, self.k = t, k

    def __eq__(self, o):
        if isinstance(o, Other):
            raise Unknown("an unspecified value looked at")
        return isinstance(o, UV) and self.t == o.t and self.k == o.k

    def __hash__(self):
        return hash(("UV", self.t, self.k))

    def __repr__(self):
        return self.k


class Fn:
    """a HOL function value"""
    __slots__ = ("f", "dom", "dk", "interp")

    def __init__(self, f, dom, interp, dk=None):
        self.f, self.dom, self.interp, self.dk = f, dom, interp, dk or tykey(dom)

    def __call__(self, x):
        return self.f(x)

    def __eq__(self, other):
        if isinstance(other, Other):
            raise Unknown("an unspecified value looked at")
        if not isinstance(other, Fn):
            return False
        d = self.interp.domain(self.dom, self.dk)
        if d is None:                                   # extensional equality over an infinite type: unknown
            raise Unknown("function equality over an infinite type")
        return all(self.f(x) == other.f(x) for x in d)

    def __hash__(self):
        return id(self)


def hkey(v):
    return id(v) if isinstance(v, Fn) else v


def has_fn(vals):
    return any(isinstance(v, Fn) for v in vals)


def curry(I, k, vals, ty, finish):
    """a constant of arity k given fewer arguments: a function waiting for the rest"""
    if len(vals) >= k:
        return finish(vals[:k], vals[k:])
    dom = arrow(ty)[0][len(vals)]
    return Fn(lambda x: curry(I, k, vals + [x], ty, finish), dom, I)


def apply_rest(f, rest):
    for x in rest:
        if not isinstance(f, Fn):
            raise Unknown("applying a non-function")
        f = f(x)
    return f


def asbool(c):
    def b(I, env):
        try:
            v = c(I, env)
        except Unknown as e:
            I.why = str(e)
            return None
        except RecursionError:
            I.why = "recursion"
            return None
        return v if v is None or v is True or v is False else None
    return b


NATIVE = {
    ("arithmetic", "+"): (2, lambda a, b: a + b),
    ("arithmetic", "-"): (2, lambda a, b: max(a - b, 0)),
    ("arithmetic", "*"): (2, lambda a, b: a * b),
    ("prim_rec", "<"): (2, lambda a, b: a < b),
    ("arithmetic", "<="): (2, lambda a, b: a <= b),
    ("arithmetic", ">"): (2, lambda a, b: a > b),
    ("arithmetic", ">="): (2, lambda a, b: a >= b),
    ("arithmetic", "DIV"): (2, lambda a, b: a // b if b else _unknown("DIV 0")),
    ("arithmetic", "MOD"): (2, lambda a, b: a % b if b else _unknown("MOD 0")),
    ("arithmetic", "EXP"): (2, lambda a, b: a ** b if b < 4096 else _unknown("EXP")),
    ("num", "SUC"): (1, lambda a: a + 1),
    ("realax", "real_of_num"): (1, lambda a: Fraction(a)),
    ("realax", "real_add"): (2, lambda a, b: a + b),
    ("realax", "real_mul"): (2, lambda a, b: a * b),
    ("realax", "real_neg"): (1, lambda a: -a),
    ("realax", "real_lt"): (2, lambda a, b: a < b),
    ("realax", "real_sub"): (2, lambda a, b: a - b),
    ("real", "real_sub"): (2, lambda a, b: a - b),
    ("real", "real_lte"): (2, lambda a, b: a <= b),
    ("real", "real_gt"): (2, lambda a, b: a > b),
    ("real", "real_ge"): (2, lambda a, b: a >= b),
    ("realax", "/"): (2, lambda a, b: a / b if b else Fraction(0)),
    ("real", "/"): (2, lambda a, b: a / b if b else Fraction(0)),
    ("real", "real_div"): (2, lambda a, b: a / b if b else Fraction(0)),
    ("string", "CHR"): (1, lambda a: a if a < 256 else _unknown("CHR")),
    ("string", "ORD"): (1, lambda a: a),
    ("list", "NIL"): (0, lambda: ()),
    ("list", "CONS"): (2, lambda a, b: (a,) + b),
    ("list", "APPEND"): (2, lambda a, b: a + b),
    ("list", "LENGTH"): (1, lambda a: len(a)),
}
NUM = {"kind": "type_application", "theory": "num", "name": "num", "arguments": []}
NUMK = tykey(NUM)


class Defined:
    """a defined constant at one type: its clauses, compiled"""
    def __init__(self, name, ty):
        self.name, self.ty, self.clauses = name, ty, []

    def apply(self, I, vals):
        for ci, (k, matchers, rhs) in enumerate(self.clauses):
            if len(vals) < k:
                return curry(I, k, vals, self.ty, lambda a, rest: self.apply(I, a + rest))
            env = {}
            if all(m(I, v, env) for m, v in zip(matchers, vals[:k])):
                args = vals[:k]
                key = (id(self), ci, tuple(args)) if not has_fn(args) and not has_fn(env.values()) else None
                if key is not None and key in I.ucache:
                    v = I.ucache[key]
                else:
                    I.depth += 1
                    if I.depth > 300:
                        I.depth -= 1
                        raise Unknown("recursion depth")
                    try:
                        v = rhs(I, env)
                    finally:
                        I.depth -= 1
                    if key is not None:
                        I.ucache[key] = v
                if v is None and len(vals) > k:
                    raise Unknown("unknown function value")
                return apply_rest(v, vals[k:])
        raise Unknown(f"no clause of {self.name} matches")


class Semantics:
    """what does not depend on the model: the definitions, and every HOL term compiled once"""

    def __init__(self, theory, symbol, sort_of, enums, adts, ctor_z3, enum_z3, clauses, symbols=None):
        self.theory, self.symbol, self.sort_of = theory, symbol, sort_of   # symbol(key) -> (z3 decl, arity) or None
        self.symbols = symbols or (lambda: [])          # every (key, z3 decl) of a primitive
        self.enums, self.adts, self.ctor_z3, self.enum_z3, self.clauses = enums, adts, ctor_z3, enum_z3, clauses
        self.ctor_type = {c: n for n, cs in enums.items() for c in cs}
        self.ctor_type.update({c: n for n, alts in adts.items() for c, _ in alts})
        self.ccache, self.dcache, self.numerals = {}, {}, set()

    def compile_top(self, t):
        e = self.ccache.get(id(t))
        if e is not None and e[0] is t:
            return e[1]
        c = asbool(self.comp(t, frozenset()))
        self.ccache[id(t)] = (t, c)                    # the term is kept, so its id is not reused
        return c

    def comp(self, t, scope):
        k = t["kind"]
        if k == "variable":
            n = t["name"]
            if n in scope:
                return lambda I, env: env[n]
            return self.comp_const({"kind": "constant", "theory": self.theory, "name": n, "type": t["type"]}, [], scope)
        if k == "constant":
            return self.comp_const(t, [], scope)
        if k == "abstraction":
            vn, vty = t["variable"]["name"], t["variable"]["type"]
            vk = tykey(vty)
            body = self.comp(t["body"], scope | {vn})
            return lambda I, env: Fn(lambda x: body(I, {**env, vn: x}), vty, I, vk)
        h, args = strip_comb(t)
        if h["kind"] == "constant":
            return self.comp_const(h, args, scope)
        if h["kind"] == "variable" and h["name"] not in scope:
            return self.comp_const({"kind": "constant", "theory": self.theory, "name": h["name"], "type": h["type"]}, args, scope)
        f, cs = self.comp(h, scope), [self.comp(a, scope) for a in args]
        def run(I, env):
            g = f(I, env)
            for c in cs:
                if not isinstance(g, Fn):
                    raise Unknown("applying a non-function")
                x = c(I, env)
                if x is None:
                    raise Unknown("unknown argument")
                g = g(x)
            return g
        return run

    def comp_staged(self, name, lam, scope):
        """!x1..xn. A1 /\\ .. /\\ Ak ==> C, or ?x1..xn. A1 /\\ .. /\\ Ak: nested loops over x1..xn in which each Ai is
        checked as soon as the variables it mentions are fixed (miniscoping), so a false condition skips every
        loop inside it. Three-valued like the plain quantifiers."""
        vs, body = [lam["variable"]], lam["body"]
        while True:
            h, a = strip_comb(body)
            if h["kind"] == "constant" and h["name"] == name and h.get("theory") == "bool" and len(a) == 1 \
                    and a[0]["kind"] == "abstraction" and a[0]["variable"]["name"] not in {v["name"] for v in vs}:
                vs.append(a[0]["variable"]); body = a[0]["body"]
            else:
                break
        if name == "!":
            h, a = strip_comb(body)
            if not (h["kind"] == "constant" and h["name"] == "==>" and len(a) == 2):
                return None
            conds, concl = conjuncts(a[0]), a[1]
        else:
            conds, concl = conjuncts(body), None
        if len(vs) < 2 and len(conds) < 2:
            return None                                 # nothing to gain over the plain quantifier
        names = [v["name"] for v in vs]
        inner = scope | set(names)
        stages = [[] for _ in range(len(vs) + 1)]        # stage k: conditions whose last chain variable is x_k
        cond_info = []                                  # (compiled condition, the chain variables it mentions)
        for c in conds:
            fv = free_vars(c) & set(names)
            k = max((names.index(x) + 1 for x in fv), default=0)
            cc = asbool(self.comp(c, inner))
            stages[k].append(cc)
            cond_info.append((cc, fv))
        C = asbool(self.comp(concl, inner)) if concl is not None else None
        tys = [(v["type"], tykey(v["type"])) for v in vs]
        n = len(vs)
        # Guarded evaluation. A condition that is a declared predicate applied to chain variables (and terms without
        # them) holds only at the true rows of its table in the model. When the table's default is false, the loops
        # run over those rows instead of every combination of values, as a database joins on a relation rather than
        # scanning a cross product; the answer is the same.
        guard = None
        for c in conds:
            gh, gargs = strip_comb(c)
            if gh["kind"] != "constant" or gh.get("theory") != self.theory or not gargs:
                continue
            if gh["name"] in self.ctor_type or (gh.get("theory"), gh["name"]) in self.clauses:
                continue
            gdom, grng = arrow(gh["type"])
            if grng.get("name") != "bool" or len(gargs) != len(gdom) or any(is_fun(d) for d in gdom):
                continue
            specs, bound = [], set()
            for x in gargs:
                if x["kind"] == "variable" and x["name"] in names:
                    specs.append(("var", x["name"])); bound.add(x["name"])
                elif not (free_vars(x) & set(names)):
                    specs.append(("term", self.comp(x, scope)))
                else:
                    break
            else:
                if bound and (guard is None or len(bound) > len(guard[3])):
                    guard = ((gh["name"], tykey(gh["type"])), gdom, specs, bound)
        if guard is not None:
            rest = [i for i, nm in enumerate(names) if nm not in guard[3]]
            # for the variables the guard leaves open: each condition at the first point all its variables are bound
            at = [[] for _ in range(len(rest) + 1)]
            for cc, fv in cond_info:
                k = max((rest.index(names.index(x)) + 1 for x in fv if x not in guard[3]), default=0)
                at[k].append(cc)

        def via_rows(I, env, forall):
            """the quantifier over the guard's true rows; NotImplemented when the table has no finite set of them"""
            rows = I.true_rows(guard[0], guard[1])
            if rows is None:
                return NotImplemented
            res = True if forall else False
            for row in rows:
                bind, ok = {}, True
                for (kind, x), v in zip(guard[2], row):
                    if kind == "var":
                        if x in bind and not (bind[x] == v):
                            ok = False; break
                        bind[x] = v
                    else:
                        tv = x(I, env)
                        if tv is None or not (tv == v):
                            ok = False; break
                if not ok:
                    continue
                r = rest_loop(I, {**env, **bind}, 0, False, forall)
                if forall and r is False:
                    return False
                if not forall and r is True:
                    return True
                if r is None:
                    res = None
            return res

        def rest_loop(I, env, k, unk, forall):
            st = check(at[k], I, env)
            if st is False:
                return True if forall else False
            unk = unk or st is None
            if k == len(rest):
                if forall:
                    c = C(I, env)
                    return True if c is True else (None if unk or c is None else False)
                return None if unk else True
            if time.time() > I.deadline:
                raise Unknown("evaluation time")
            i = rest[k]
            vals, exact = I.values(*tys[i])
            res = True if forall else False
            for x in vals:
                r = rest_loop(I, {**env, names[i]: x}, k + 1, unk, forall)
                if forall and r is False:
                    return False
                if not forall and r is True:
                    return True
                if r is None:
                    res = None
            if not exact:
                return (None if res is not False else False) if forall else (res if res is True else None)
            return res
        def check(cs, I, env):
            res = True
            for c in cs:
                v = c(I, env)
                if v is False:
                    return False
                if v is None:
                    res = None
            return res
        if name == "!":
            def loop(I, env, k, unk):
                if k > n:
                    c = C(I, env)
                    return True if c is True else (None if unk or c is None else False)
                if time.time() > I.deadline:
                    raise Unknown("evaluation time")
                vals, exact = I.values(*tys[k - 1])
                res = True
                for x in vals:
                    e2 = {**env, names[k - 1]: x}
                    st = check(stages[k], I, e2)
                    if st is False:
                        continue                        # the condition fails: true for every value inside
                    r = loop(I, e2, k + 1, unk or st is None)
                    if r is False:
                        return False
                    if r is None:
                        res = None
                return res if exact else (None if res is not False else False)
            def forall(I, env):
                if guard is not None:
                    r = via_rows(I, env, True)
                    if r is not NotImplemented:
                        return r
                st = check(stages[0], I, env)
                return True if st is False else loop(I, env, 1, st is None)
            return forall
        def loop(I, env, k, unk):
            if k > n:
                return None if unk else True
            if time.time() > I.deadline:
                raise Unknown("evaluation time")
            vals, exact = I.values(*tys[k - 1])
            res = False
            for x in vals:
                e2 = {**env, names[k - 1]: x}
                st = check(stages[k], I, e2)
                if st is False:
                    continue
                r = loop(I, e2, k + 1, unk or st is None)
                if r is True:
                    return True
                if r is None:
                    res = None
            return res if exact else None
        def exists(I, env):
            if guard is not None:
                r = via_rows(I, env, False)
                if r is not NotImplemented:
                    return r
            st = check(stages[0], I, env)
            return False if st is False else loop(I, env, 1, st is None)
        return exists

    def numeral(self, t):
        h, a = strip_comb(t)
        n = h.get("name")
        if n == "NUMERAL":
            return self.numeral(a[0])
        if n in ("ZERO", "0"):
            return 0
        if n == "BIT1":
            return 2 * self.numeral(a[0]) + 1
        if n == "BIT2":
            return 2 * self.numeral(a[0]) + 2
        raise Unknown("numeral")

    def comp_const(self, h, args, scope):
        name, thy, ty = h["name"], h.get("theory"), h["type"]
        n = len(args)
        B = lambda a, sc=scope: asbool(self.comp(a, sc))
        if thy == "bool" and name in ("T", "F") and n == 0:
            v = name == "T"
            return lambda I, env: v
        if thy == "bool" and name == "~" and n == 1:
            a = B(args[0])
            def neg(I, env):
                x = a(I, env)
                return None if x is None else not x
            return neg
        if thy == "bool" and name == "/\\" and n == 2:
            a, b = B(args[0]), B(args[1])
            def conj(I, env):
                x = a(I, env)
                if x is False: return False
                y = b(I, env)
                if y is False: return False
                return True if x is True and y is True else None
            return conj
        if thy == "bool" and name == "\\/" and n == 2:
            a, b = B(args[0]), B(args[1])
            def disj(I, env):
                x = a(I, env)
                if x is True: return True
                y = b(I, env)
                if y is True: return True
                return False if x is False and y is False else None
            return disj
        if thy == "min" and name == "==>" and n == 2:
            a, b = B(args[0]), B(args[1])
            def imp(I, env):
                x = a(I, env)
                if x is False: return True
                y = b(I, env)
                if y is True: return True
                return False if x is True and y is False else None
            return imp
        if thy == "bool" and name in ("!", "?") and n == 1 and args[0]["kind"] == "abstraction":
            staged = self.comp_staged(name, args[0], scope)
            if staged is not None:
                return staged
        if thy == "bool" and name in ("!", "?", "?!") and n == 1:
            if args[0]["kind"] == "abstraction":
                vn, vty = args[0]["variable"]["name"], args[0]["variable"]["type"]
                vk, body = tykey(vty), B(args[0]["body"], scope | {vn})
                return lambda I, env: I.quant(name, vty, vk, lambda x: body(I, {**env, vn: x}))
            P, vty = self.comp(args[0], scope), arrow(ty)[0][0]["arguments"][0]
            vk = tykey(vty)
            def q(I, env):
                p = P(I, env)
                if not isinstance(p, Fn):
                    raise Unknown("quantifier over a non-function")
                return I.quant(name, vty, vk, p)
            return q
        if thy == "min" and name == "=" and n == 2:
            if arrow(ty)[0][0].get("name") == "bool":
                a, b = B(args[0]), B(args[1])
                def beq(I, env):
                    x, y = a(I, env), b(I, env)
                    return None if x is None or y is None else x == y
                return beq
            ca, cb = self.comp(args[0], scope), self.comp(args[1], scope)
            def eq(I, env):
                try:
                    return ca(I, env) == cb(I, env)
                except Unknown as e:
                    I.why = str(e)
                    return None
            return eq
        if thy == "bool" and name == "COND" and n == 3:
            c, x, y = B(args[0]), self.comp(args[1], scope), self.comp(args[2], scope)
            def cond(I, env):
                v = c(I, env)
                if v is None:
                    raise Unknown("condition unknown")
                return x(I, env) if v else y(I, env)
            return cond
        if thy == "bool" and name == "LET" and n == 2:
            f, x = self.comp(args[0], scope), self.comp(args[1], scope)
            return lambda I, env: apply_rest(f(I, env), [x(I, env)])
        if (thy, name) in (("min", "@"), ("bool", "ARB")):
            return lambda I, env: _unknown(name)
        if name in ("NUMERAL", "BIT1", "BIT2", "ZERO") or (thy == "num" and name == "0" and n == 0):
            try:
                v = self.numeral(rebuild(h, args))
            except Unknown:
                return lambda I, env: _unknown("numeral")
            self.numerals.add(v)
            return lambda I, env: v
        cs = [self.comp(a, scope) for a in args]
        target = self.const_fn(h)
        def strict(I, env):
            vals = []
            for c in cs:
                v = c(I, env)
                if v is None:
                    raise Unknown("unknown argument")
                vals.append(v)
            return target(I, vals)
        return strict

    def const_fn(self, h):
        """(interp, argument values) -> value, for a constant that is not a logical operator"""
        name, thy, ty = h["name"], h.get("theory"), h["type"]
        if (thy, name) in NATIVE:
            k, f = NATIVE[(thy, name)]
            def native(a, rest):
                try:
                    v = f(*a)
                except (TypeError, ZeroDivisionError, OverflowError) as e:
                    raise Unknown(f"{name}: {e}")
                return apply_rest(v, rest)
            return lambda I, vals: curry(I, k, vals, ty, native)
        if thy == self.theory and name in self.ctor_type:            # a datatype constructor builds a value
            tn = self.ctor_type[name]
            k = 0 if tn in self.enums else len(dict(self.adts[tn])[name])
            return lambda I, vals: curry(I, k, vals, ty, lambda a, rest: apply_rest(DV(name, a), rest))
        if thy == self.theory and name.endswith("_CASE") and name[:-5] in self.enums:
            cs = self.enums[name[:-5]]                  # T_CASE x v1 .. vn is the v of x's constructor
            def pick(a, rest):
                if not isinstance(a[0], DV) or a[0].c not in cs:
                    raise Unknown("case of a non-constructor")
                return apply_rest(a[1 + cs.index(a[0].c)], rest)
            return lambda I, vals: curry(I, 1 + len(cs), vals, ty, pick)
        if (thy, name) in self.clauses:
            d = self.defined(h)
            return d.apply
        if thy != self.theory:
            return lambda I, vals: _unknown(f"library constant {thy}${name} without a definition")
        dom, rng = arrow(ty)
        if any(is_fun(d) for d in dom):
            return lambda I, vals: _unknown("primitive taking a function")
        key, k = (name, tykey(ty)), len(dom)
        return lambda I, vals: curry(I, k, vals, ty, lambda a, rest: apply_rest(I.primitive(key, dom, rng, k, a), rest))

    def defined(self, h):
        name, thy, ty = h["name"], h.get("theory"), h["type"]
        key = (thy, name, tykey(ty))
        if key in self.dcache:
            return self.dcache[key]
        d = Defined(name, ty)
        self.dcache[key] = d                            # before compiling, so recursion finds it
        for hty, vs, pats, rhs in self.clauses[(thy, name)]:
            sub = match_ty(hty, ty, {})
            if sub is None:
                continue
            bound = frozenset(v["name"] for v in vs) | frozenset(x for p in pats for x in pattern_vars(p))
            d.clauses.append((len(pats), [self.comp_pat(subst_term(p, sub)) for p in pats], self.comp(subst_term(rhs, sub), bound)))
        return d

    def comp_pat(self, p):
        """(interp, value, env) -> does the value match, binding the pattern's variables in env"""
        if p["kind"] == "variable":
            n = p["name"]
            def var(I, v, env):
                if n in env:
                    return env[n] == v
                env[n] = v
                return True
            return var
        h, args = strip_comb(p)
        if h["kind"] != "constant":
            return lambda I, v, env: _unknown("pattern")
        name, thy = h["name"], h.get("theory")
        if name in ("NUMERAL", "ZERO", "BIT1", "BIT2") or (thy == "num" and name == "0"):
            k = self.numeral(p)
            return lambda I, v, env: v == k
        if thy == "num" and name == "SUC" and len(args) == 1:
            m = self.comp_pat(args[0])
            return lambda I, v, env: (_unknown("pattern on an unspecified value") if isinstance(v, Other) else
                                      isinstance(v, int) and not isinstance(v, bool) and v > 0 and m(I, v - 1, env))
        if thy == "list" and name == "NIL":
            return lambda I, v, env: (_unknown("pattern on an unspecified value") if isinstance(v, Other) else v == ())
        if thy == "list" and name == "CONS" and len(args) == 2:
            mh, mt = self.comp_pat(args[0]), self.comp_pat(args[1])
            return lambda I, v, env: (_unknown("pattern on an unspecified value") if isinstance(v, Other) else
                                      type(v) is tuple and len(v) > 0 and mh(I, v[0], env) and mt(I, v[1:], env))
        if thy == "bool" and name in ("T", "F"):
            b = name == "T"
            return lambda I, v, env: v == b
        if thy == self.theory and name in self.ctor_type:
            ms = [self.comp_pat(a) for a in args]
            def ctor(I, v, env):
                if not isinstance(v, DV):
                    raise Unknown("pattern against a non-constructor value")
                return v.c == name and len(v.a) == len(ms) and all(m(I, x, env) for m, x in zip(ms, v.a))
            return ctor
        return lambda I, v, env: _unknown("pattern " + name)


class Interp:
    """one interpretation, built from one Z3 model"""

    def __init__(self, sem, model, seconds=20.0):
        import z3
        self.z3, self.sem, self.m = z3, sem, model
        self.domains, self.elems, self.prim, self.ucache, self.tables, self.decl_ids = {}, {}, {}, {}, {}, None
        self.rows = {}
        self.seen = {NUMK: set(sem.numerals) | {0, 1}}
        self.depth, self.why, self.deadline = 0, None, time.time() + seconds

    def evb(self, t):
        """a truth value for a closed HOL term: True, False or None (unknown)"""
        return self.sem.compile_top(t)(self, {})

    # ---- types
    def hol_name_ty(self, a):
        if a == "string":
            return {"kind": "type_application", "name": "list", "arguments": [{"kind": "type_application", "name": "char", "arguments": []}]}
        return {"kind": "type_application", "name": a, "arguments": []}

    def is_usort(self, ty):
        s = self.sem
        if ty.get("kind") != "type_application":
            return True                                 # a type variable: the universe Z3 gives its sort
        return not ty["arguments"] and ty["name"] not in \
            ("bool", "num", "int", "real", "char", "string", "list", "fun") and ty["name"] not in s.enums \
            and ty["name"] not in s.adts

    def finite_adt(self, n, seen=()):
        s = self.sem
        if n in seen or n not in s.adts:
            return n in s.enums
        for c, args in s.adts[n]:
            for a in args:
                if a in seen + (n,) or not (a == "bool" or a in s.enums or (a in s.adts and self.finite_adt(a, seen + (n,)))
                                            or self.is_usort(self.hol_name_ty(a))):
                    return False
        return True

    def domain(self, ty, tk=None):
        """the values of a finite type, in a fixed order; None for an infinite type"""
        tk = tk or tykey(ty)
        if tk in self.domains:
            return self.domains[tk]
        s, d = self.sem, None
        if ty.get("kind") != "type_application":
            d = self.universe(ty, "'" + str(ty.get("name", "a")).strip("'"))
        elif ty["name"] == "bool":
            d = [False, True]
        elif ty["name"] in s.enums:
            d = [DV(c, ()) for c in s.enums[ty["name"]]]
        elif ty["name"] in s.adts and self.finite_adt(ty["name"]):
            d = []
            for c, args in s.adts[ty["name"]]:
                tuples = [()]
                for a in args:
                    ad = self.domain(self.hol_name_ty(a))
                    tuples = [t + (v,) for t in tuples for v in ad]
                    if len(tuples) > 5000:
                        raise Unknown("datatype too large to enumerate")
                d += [DV(c, t) for t in tuples]
        elif is_fun(ty):
            dd, rd = self.domain(ty["arguments"][0]), self.domain(ty["arguments"][1])
            if dd is not None and rd is not None and len(rd) ** len(dd) <= 4096:
                d = []
                for i in range(len(rd) ** len(dd)):
                    table, x = {}, i
                    for v in dd:
                        table[hkey(v)] = rd[x % len(rd)]; x //= len(rd)
                    d.append(Fn(lambda v, table=table: table[hkey(v)], ty["arguments"][0], self))
        elif self.is_usort(ty):
            d = self.universe(ty, ty["name"])
        self.domains[tk] = d
        return d

    def universe(self, ty, name):
        univ = self.m.get_universe(self.sem.sort_of(ty))
        if not univ:
            return [UV(name, "__default")]            # the model says nothing about this type: one element
        d = []
        for e in univ:
            v = UV(name, str(e)); self.elems[v] = e; d.append(v)
        return d

    def tyname(self, ty):
        return ty.get("name") if ty.get("kind") == "type_application" else "'" + str(ty.get("name", "a")).strip("'")

    def table_values(self, ty, tk):
        """S: every value of type ty at an argument place of type ty in the model's table of some primitive"""
        if tk in self.tables:
            return self.tables[tk]
        z3, S = self.z3, set()
        for key, f in self.sem.symbols():
            dom = arrow(json.loads(key[1]))[0]
            places = [i for i, d in enumerate(dom) if tykey(d) == tk]
            if not places:
                continue
            if not self.has(f):                         # not in the model: no table yet, so no entries
                continue
            fi = self.m[f]
            for k in range(fi.num_entries()):
                ent = fi.entry(k)
                for i in places:
                    S.add(self.to_py(ent.arg_value(i), ty))
            e = fi.else_value()
            if e is not None:
                lits, _ = self.default_shape(e)
                for i in places:
                    S |= {self.to_py(v, ty) for v in lits.get(i, ())}
        self.tables[tk] = S
        return S

    COMPARE = None

    def default_shape(self, e):
        """in a table's default: the literal values each argument place i is compared with (Var(i) op value), and
        the places used in any other way"""
        z3 = self.z3
        if Interp.COMPARE is None:
            Interp.COMPARE = {z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT}
        lits, other = {}, set()
        def is_lit(x):
            return z3.is_int_value(x) or z3.is_rational_value(x) or z3.is_true(x) or z3.is_false(x)
        stack = [e]
        while stack:
            x = stack.pop()
            if z3.is_var(x):
                other.add(z3.get_var_index(x)); continue
            if z3.is_app(x) and x.decl().kind() in Interp.COMPARE and x.num_args() == 2:
                a, b = x.arg(0), x.arg(1)
                if z3.is_var(a) and is_lit(b):
                    lits.setdefault(z3.get_var_index(a), []).append(b); continue
                if z3.is_var(b) and is_lit(a):
                    lits.setdefault(z3.get_var_index(b), []).append(a); continue
            stack.extend(x.children())
        return lits, other

    def default(self, ty):
        if ty.get("kind") != "type_application":
            return self.domain(ty)[0]
        n, s = ty["name"], self.sem
        if n == "bool":
            return False
        if n in ("num", "int", "char"):
            return 0
        if n == "real":
            return Fraction(0)
        if n == "list":
            return ()
        if is_fun(ty):
            r = self.default(ty["arguments"][1])
            return Fn(lambda x: r, ty["arguments"][0], self)
        d = self.domain(ty)
        if d:
            return d[0]
        if n in s.adts:
            for c, args in s.adts[n]:
                if all(a not in s.adts for a in args):
                    return DV(c, [self.default(self.hol_name_ty(a)) for a in args])
        raise Unknown("no default value for " + n)

    def values(self, ty, tk):
        """the values a quantifier over ty runs through, and whether they stand for every value of ty"""
        d = self.domain(ty, tk)
        if d is not None:
            return d, True
        try:
            S = self.table_values(ty, tk) | self.seen.get(tk, set())
            if ty.get("name") in ("num", "int"):
                S = S | self.sem.numerals | {0}
                pts = sorted(S)
                gaps = [Other(tk, a, b) for a, b in zip(pts, pts[1:]) if b - a > 1] + [Other(tk, pts[-1], None)]
                if ty["name"] == "int":
                    gaps.append(Other(tk, None, pts[0]))
                return pts + gaps, True
            return list(S) + [Other(tk)], True
        except Unknown:
            d = list(self.seen.get(tk, ()))
            try:
                d.append(self.default(ty))
            except Unknown:
                pass
            return d, False

    def quant(self, name, ty, tk, body):
        """! ? ?! over the values of ty; body maps a value to a truth value"""
        if time.time() > self.deadline:
            raise Unknown("evaluation time")
        d = self.domain(ty, tk)
        finite = d is not None
        if not finite:
            try:
                S = self.table_values(ty, tk) | self.seen.get(tk, set())
                if ty.get("name") in ("num", "int"):
                    S = S | self.sem.numerals | {0}
                    pts = sorted(S)
                    gaps = [Other(tk, a, b) for a, b in zip(pts, pts[1:]) if b - a > 1] + [Other(tk, pts[-1], None)]
                    if ty["name"] == "int":
                        gaps.append(Other(tk, None, pts[0]))
                    d = pts + gaps
                else:
                    d = list(S) + [Other(tk)]
                finite = True                           # S one by one, and Other for every value outside it
            except Unknown:
                d = list(self.seen.get(tk, ()))
                try:
                    d.append(self.default(ty))
                except Unknown:
                    pass
        vals = []
        for x in d:
            try:
                v = body(x)
            except Unknown:
                v = None
            if v is not None and v is not True and v is not False:
                v = None
            if name == "!" and v is False:
                return False
            if name == "?" and v is True:
                return True
            vals.append(v)
            if name == "?!" and sum(1 for y in vals if y is True) >= 2:
                return False
        if name == "?!" and any(isinstance(x, Other) for x in d):
            return None                                 # Other stands for many values: it cannot be the unique one
        if not finite:
            self.why = "quantifier over an infinite type, not settled by the values met"
            return None
        if name == "!":
            return True if all(v is True for v in vals) else None
        if name == "?":
            return False if all(v is False for v in vals) else None
        if any(v is None for v in vals):
            return None
        return sum(1 for v in vals if v) == 1

    # ---- primitive constants: their values in the model
    def primitive(self, key, dom, rng, k, a):
        ck = (key, tuple(a))
        if ck in self.prim:
            return self.prim[ck]
        sym = self.sem.symbol(key)
        if any(isinstance(x, Other) for x in a):
            v = self.at_other(sym, dom, rng, k, a)
            self.prim[ck] = v
            return v
        if sym is None:
            v = self.default(rng)                       # never constrained by the translation: any value will do
        else:
            f, arity = sym
            if arity != k:
                raise Unknown("arity")
            e = f(*[self.to_z3(x, d) for x, d in zip(a, dom)]) if k else f
            v = self.to_py(self.m.eval(e, model_completion=True), rng)
        self.prim[ck] = v
        return v

    def at_other(self, sym, dom, rng, k, a):
        """a primitive at arguments that include Other: no table entry can match, so its default value, if that
        default does not depend on the arguments"""
        z3 = self.z3
        if sym is None:
            return self.default(rng)                    # never constrained: one value everywhere will do
        f, arity = sym
        if arity != k or k == 0:
            raise Unknown("arity")
        if not self.has(f):                             # let model completion give it a table, then read the default
            self.m.eval(f(*[self.to_z3(self.default(d), d) for d in dom]), model_completion=True)
            self.decl_ids = None
            if not self.has(f):
                raise Unknown("no table for a primitive")
        e = self.m[f].else_value()
        if e is None:
            raise Unknown("a table without a default")
        others = {i for i, x in enumerate(a) if isinstance(x, Other)}
        lits, used = self.default_shape(e)
        used |= set(lits)
        reps = {}
        for i in others & used:
            o = a[i]                                    # the default compares argument i with literals only, all
            if i in self.default_shape(e)[1] or o.lo is None and o.hi is None:   # of them in S, so any point of
                raise Unknown("a table default that depends on an unspecified argument")   # the gap gives the same
            r = o.lo + 1 if o.lo is not None else o.hi - 1
            if o.hi is not None and r >= o.hi:
                raise Unknown("an empty gap")
            reps[i] = r
        if used:                                        # Var(i) is argument i
            e = z3.substitute_vars(e, *[self.to_z3(reps[i] if i in reps else self.default(d) if i in others else x, d)
                                        for i, (x, d) in enumerate(zip(a, dom))])
        return self.to_py(self.m.eval(e, model_completion=True), rng)

    def true_rows(self, key, dom):
        """the argument tuples where the declared predicate key holds, when its table's default is false; None
        otherwise (then it may hold at arguments the table does not list)"""
        if key in self.rows:
            return self.rows[key]
        z3 = self.z3
        sym = self.sem.symbol(key)
        if sym is None:
            rows = []                                   # never constrained: false everywhere, as primitive() reads it
        else:
            f, arity = sym
            if arity != len(dom):
                raise Unknown("arity")
            if not self.has(f):                         # let model completion give it its (constant) table
                self.m.eval(f(*[self.to_z3(self.default(d), d) for d in dom]), model_completion=True)
                self.decl_ids = None
                if not self.has(f):
                    raise Unknown("no table for a primitive")
            fi = self.m[f]
            e = fi.else_value()
            if e is None or not z3.is_false(e):
                rows = None
            else:
                rows = []
                for k in range(fi.num_entries()):
                    ent = fi.entry(k)
                    if z3.is_true(ent.value()):
                        rows.append(tuple(self.to_py(ent.arg_value(i), d) for i, d in enumerate(dom)))
                    elif not z3.is_false(ent.value()):
                        rows = None
                        break
        self.rows[key] = rows
        return rows

    def has(self, f):
        """does the model interpret f? (z3py gives an empty table, not None, for a function it does not)"""
        if self.decl_ids is None:
            self.decl_ids = {d.get_id() for d in self.m.decls()}
        return f.get_id() in self.decl_ids

    def to_py(self, e, ty):
        z3, s = self.z3, self.sem
        n = ty.get("name")
        if n == "bool":
            if z3.is_true(e): return True
            if z3.is_false(e): return False
            raise Unknown("bool value")
        if n in ("num", "int", "char"):
            if not z3.is_int_value(e):
                raise Unknown("int value")
            v = e.as_long()
            if (n == "num" and v < 0) or (n == "char" and not 0 <= v < 256):
                raise Unknown("illegal value")          # the translation must never give HOL an illegal value
            self.seen.setdefault(tykey(ty), set()).add(v)
            return v
        if n == "real":
            if not z3.is_rational_value(e):
                raise Unknown("real value")
            return Fraction(e.numerator_as_long(), e.denominator_as_long())
        if n == "list":
            el = ty["arguments"][0]
            out = []
            def walk(x):
                kind = x.decl().kind()
                if kind == z3.Z3_OP_SEQ_CONCAT:
                    for c in x.children(): walk(c)
                elif kind == z3.Z3_OP_SEQ_UNIT:
                    out.append(self.to_py(x.children()[0], el))
                elif kind == z3.Z3_OP_SEQ_EMPTY:
                    pass
                else:
                    raise Unknown("sequence value")
            walk(e)
            v = tuple(out)
            self.seen.setdefault(tykey(ty), set()).add(v)
            return v
        if n in s.enums:
            c = e.decl().name()
            if c not in s.enums[n]:
                raise Unknown("enumeration value")
            return DV(c, ())
        if n in s.adts:
            c = e.decl().name()
            alts = dict(s.adts[n])
            if c not in alts:
                raise Unknown("datatype value")
            v = DV(c, [self.to_py(x, self.hol_name_ty(a)) for x, a in zip(e.children(), alts[c])])
            self.seen.setdefault(tykey(ty), set()).add(v)
            return v
        if self.is_usort(ty):
            d = self.domain(ty)
            v = UV(self.tyname(ty), str(e))
            if v not in d:
                raise Unknown("element outside the universe")
            return v
        raise Unknown("value of type " + str(n))

    def to_z3(self, v, ty):
        z3, s = self.z3, self.sem
        if isinstance(v, Other):
            raise Unknown("an unspecified value looked at")
        n = ty.get("name")
        if n == "bool":
            return z3.BoolVal(v)
        if n in ("num", "int", "char"):
            return z3.IntVal(v)
        if n == "real":
            return z3.RealVal(f"{v.numerator}/{v.denominator}")
        if n == "list":
            el = ty["arguments"][0]
            if not v:
                return z3.Empty(z3.SeqSort(s.sort_of(el)))
            parts = [z3.Unit(self.to_z3(x, el)) for x in v]
            return parts[0] if len(parts) == 1 else z3.Concat(*parts)
        if n in s.enums:
            return s.enum_z3[(v.c, n)]
        if n in s.adts:
            alts = dict(s.adts[n])
            c = s.ctor_z3[v.c]
            return c(*[self.to_z3(x, self.hol_name_ty(a)) for x, a in zip(v.a, alts[v.c])]) if alts[v.c] else c
        if self.is_usort(ty):
            if v not in self.elems:
                raise Unknown("element with no Z3 counterpart")
            return self.elems[v]
        raise Unknown("no Z3 value for type " + str(n))
