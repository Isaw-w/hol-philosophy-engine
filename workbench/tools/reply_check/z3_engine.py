"""The checked HOL4 argument, translated once into Z3, and every question about it answered with three states.
No model call.

  python3 tools/reply_check/z3_engine.py runs/DATE/RUN             # runs on the mini, writes RUN/z3_engine/
  python3 tools/reply_check/z3_engine.py runs/DATE/RUN --local     # runs here (needs the z3 Python package)

Starting points are final's stated premises and the source's axioms; definitions are always on. Each starting point
gets a switch, so one solver answers "do these starting points give this conclusion?" for any subset:
  follows        Z3 finds no way for the starting points to hold and the conclusion fail (an unsat core is kept)
  does not       Z3 finds a model where they hold and the conclusion fails, and the model holds up in HOL semantics:
                 the original HOL statements, read in it, are true and the conclusion false (hol_semantics.py)
  unknown        Z3 gives up within the time limit, a term cannot be translated, or a countermodel does not hold up
Nothing is counted as "does not follow" without a countermodel. All smallest supports are found with MARCO
(Liffiton et al. 2016); the list is called complete only if no question on the way came back unknown.

Every-position test (Chisholm's substitution criterion, run on every argument place of every declared predicate,
since the words for attitudes and speech acts cannot be listed but one argument's places can). Inside each smallest
support of a conclusion, the facts where a constant e fills place k of predicate P are changed: dropped, or e there
replaced by an unknown thing, or by an unknown thing with e's truth value. The place is transparent when the
conclusion survives the replacement (what fills it does not matter, or only its truth value does) and opaque when Z3
finds a countermodel (which thing fills it matters).

Generality (a measure): how many principles (starting points with a quantifier or an "if", and definitions) name
particular things, such as a person, an act or a number.

Collapse and explosion under violation (hard flaws agreed in deontic logic; Chisholm 1963, Carmo and Jones 2002,
LogiKEy 2020): a predicate forced to hold of exactly what happens; principles that alone settle whether an evaluated
eventuality happens, so that a violation would make the starting points contradict each other.

Creative definitions (a hard flaw; Belnap 1993): a predicate given two explicit definitions whose bodies nothing
else in the argument makes equivalent, so that the definitions themselves assert something.

Contents given as text (a hard flaw): a constant or constructor that makes an eventuality or a content out of a string.

Misused logic (a hard flaw): a declared constant with no definition that takes a truth value. Also listed: conditional
conclusions true only because their 'if' part is ruled out, and different names forced to be one thing.

Restated premises: a premise repeated as it stands in the final is listed, not counted; a premise that says a conclusion
in other words, only through the definitions and the biconditional starting points, gets a warning.

Translation: bool is Bool; num is Int; a type declared with only nullary constructors is a Z3 enumeration; every
other type is an uninterpreted sort, so its domain stays open. Constants and functions are uninterpreted. A term
that cannot be translated (a lambda outside a quantifier, a set, a higher-order quantifier) makes the statements
that contain it untranslatable; they are listed and left out, which the report says.
"""
import argparse, itertools, json, re, shlex, subprocess, sys, time, uuid
from pathlib import Path

HERE = Path(__file__).resolve()
import os
VENV_PY = os.environ.get("HOLVERIFY_REMOTE_PYTHON", "~/thick_training/venv_logreco/bin/python3")  # z3-solver on the host


class Untranslatable(Exception):
    pass


def datatypes(source):
    """{type name: [constructor names]} for declared types whose constructors all take no arguments"""
    found = {}
    bodies = [m.group(1) or m.group(2) for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S)]
    for body in bodies:
        for decl in re.split(r";|\n(?=\s*\w+\s*=)", body):
            if "=" not in decl or "<|" in decl:
                continue
            name, rhs = decl.split("=", 1)
            alts = [a.strip() for a in rhs.split("|") if a.strip()]
            if alts and all(re.fullmatch(r"[A-Za-z_][\w']*", a) for a in alts):
                found[name.strip()] = alts
    return found


def datatypes_full(source):
    """{type name: [(constructor, [argument type names])]} for declared datatypes whose argument types are plain
    names (recursive ones included); a declaration with any other syntax is left out and stays uninterpreted"""
    found = {}
    bodies = [m.group(1) or m.group(2) for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S)]
    for body in bodies:
        for decl in re.split(r";|\n(?=\s*\w+\s*=)", body):
            if "=" not in decl or "<|" in decl:
                continue
            name, rhs = decl.split("=", 1)
            alts, ok = [], True
            for alt in [a.strip() for a in rhs.split("|") if a.strip()]:
                toks = alt.split()
                if not all(re.fullmatch(r"[A-Za-z_][\w']*", t) for t in toks):
                    ok = False; break
                alts.append((toks[0], toks[1:]))
            if ok and alts:
                found[name.strip()] = alts
    return found


def run_engine(ast, source, time_ms, budget_s=900, marco_cap=1000):
    """budget_s: once this many seconds have passed, every further question is answered unknown at once, so the run
    always ends; marco_cap: at most this many MARCO steps per conclusion. Both leave the lists marked not settled."""
    import z3
    ast = {**ast, "theorem_values": ast.get("theorem_values", []), "theorems": ast.get("theorems", [])}   # older exports
    deadline = time.time() + budget_s
    limits = {"budget": False, "marco": False, "supports": False}
    support_cap = 50
    z3.set_param("smt.macro_finder", True)          # definitions P x = body are expanded as macros, not searched as quantified axioms
    enums = datatypes(source)
    sorts, funcs = {}, {}

    def sort_of(ty):
        if ty["kind"] != "type_application":
            # a type variable: one uninterpreted sort stands for it (the instance HOL4's theorem also covers)
            tv = "tyvar_" + str(ty.get("name", "a")).strip("'")
            if tv not in sorts:
                sorts[tv] = z3.DeclareSort(tv)
            return sorts[tv]
        name, args = ty["name"], ty["arguments"]
        if name == "bool":
            return z3.BoolSort()
        if name == "num":
            return z3.IntSort()
        if name == "real":
            return z3.RealSort()
        if name == "char":
            return z3.IntSort()                         # a character is its code
        if name == "list" and len(args) == 1:
            return z3.SeqSort(sort_of(args[0]))         # lists, and strings (lists of characters), are sequences
        if name == "fun":
            raise Untranslatable("function value")
        if args:
            raise Untranslatable("type " + name)
        if name not in sorts:
            if name in adts:
                make_adts()
                return sorts[name]
            if name in enums:
                s, consts = z3.EnumSort(name, enums[name])
                sorts[name] = s
                for c, k in zip(enums[name], consts):
                    funcs[(c, name)] = k
            else:
                sorts[name] = z3.DeclareSort(name)
        return sorts[name]

    adts = {n: alts for n, alts in datatypes_full(source).items() if n not in enums}
    ctor_of = {}
    def make_adts():
        """declare every non-enumeration datatype as a Z3 algebraic datatype (recursion and mutual recursion
        allowed), so its constructors are distinct and injective as in HOL4"""
        if not adts or any(n in sorts for n in adts):
            return
        dts = {n: z3.Datatype(n) for n in adts}
        for n, alts in adts.items():
            for c, args in alts:
                fields = []
                for k, a in enumerate(args):
                    fs = dts[a] if a in dts else (z3.SeqSort(z3.IntSort()) if a == "string" else
                                                 sort_of({"kind": "type_application", "name": a, "arguments": []}))
                    fields.append((f"{c}__{k}", fs))
                dts[n].declare(c, *fields)
        for n, srt in zip(dts, z3.CreateDatatypes(*dts.values())):
            sorts[n] = srt
            for c, args in adts[n]:
                ctor_of[c] = (getattr(srt, c), len(args))

    # Legal values. Some HOL types are smaller than the Z3 sort that stands for them: num is the integers >= 0, char
    # the codes 0..255, and a list or datatype holding them only the values whose parts are legal. Every quantifier,
    # lifted lambda, bridge and extensionality axiom ranges over legal values only, and every constant and function
    # value is legal, so each HOL model extends to a model of the translation (the illegal values are left free).
    # Without this, (\n:num. 0 <= n) = (\n:num. T), a HOL4 theorem, came out inconsistent (found by an audit,
    # 2026-10-21).
    wf_funcs = {}
    def hol_name_ty(a):
        if a == "string":
            return {"kind": "type_application", "name": "list", "arguments": [{"kind": "type_application", "name": "char", "arguments": []}]}
        return {"kind": "type_application", "name": a, "arguments": []}
    def needs_wf(ty, seen=()):
        if ty["kind"] != "type_application":
            return False
        n = ty["name"]
        if n in ("num", "char"):
            return True
        if n == "list" and ty["arguments"]:
            return needs_wf(ty["arguments"][0], seen)
        if n in adts and n not in seen:
            return any(needs_wf(hol_name_ty(a), seen + (n,)) for c, args in adts[n] for a in args)
        return False
    def wf(ty, x):
        """the condition for the Z3 value x to stand for a HOL value of type ty; None when every value does"""
        if not needs_wf(ty):
            return None
        n = ty["name"]
        if n == "num":
            return x >= 0
        if n == "char":
            return z3.And(x >= 0, x < 256)
        if n == "list":
            i = z3.Int("wfi_" + uuid.uuid4().hex[:6])
            inner = wf(ty["arguments"][0], x[i])
            return z3.ForAll([i], z3.Implies(z3.And(i >= 0, i < z3.Length(x)), inner))
        return wf_adt(n)(x)
    def wf_adt(n):
        make_adts()
        if n in wf_funcs:
            return wf_funcs[n]
        srt = sorts[n]
        f = z3.RecFunction(f"wf_{n}", srt, z3.BoolSort())
        wf_funcs[n] = f
        x = z3.Const(f"wfx_{n}", srt)
        cases = []
        for k, (c, args) in enumerate(adts[n]):
            conds = [g for j, a in enumerate(args) if (g := wf(hol_name_ty(a), srt.accessor(k, j)(x))) is not None]
            cases.append(z3.Implies(srt.recognizer(k)(x), z3.And(*conds) if conds else z3.BoolVal(True)))
        z3.RecAddDefinition(f, [x], z3.And(*cases))
        return f
    def guarded(pairs):
        """the legal-value conditions for (z3 variable, HOL type) pairs, as one formula, or None"""
        conds = [g for x, ty in pairs if (g := wf(ty, x)) is not None]
        return z3.And(*conds) if conds else None
    def legal_value_axiom(f, ty):
        """the constant or function f of HOL type ty yields legal values for legal arguments"""
        dom, rng = arrow(ty)
        if not needs_wf(rng):
            return None
        if not dom:
            return wf(rng, f)
        vs = [z3.Const(f"lv{k}_" + uuid.uuid4().hex[:4], f.domain(k)) for k in range(len(dom))]
        g = guarded(list(zip(vs, dom)))
        body = wf(rng, f(*vs))
        return z3.ForAll(vs, z3.Implies(g, body) if g is not None else body)

    def arrow(ty):
        """argument types and result type of a curried function type"""
        dom = []
        while ty["kind"] == "type_application" and ty["name"] == "fun":
            dom.append(ty["arguments"][0]); ty = ty["arguments"][1]
        return dom, ty

    def strip_comb(t):
        args = []
        while t["kind"] == "application":
            args.append(t["argument"]); t = t["function"]
        return t, list(reversed(args))

    def numeral(t):
        h, a = strip_comb(t)
        n = h.get("name")
        if h["kind"] == "constant" and n == "NUMERAL":
            return numeral(a[0])
        if n == "ZERO" or n == "0":
            return 0
        if n == "BIT1":
            return 2 * numeral(a[0]) + 1
        if n == "BIT2":
            return 2 * numeral(a[0]) + 2
        raise Untranslatable("numeral")

    def const(name, ty):
        dom, rng = arrow(ty)
        if adts and not ctor_of:
            make_adts()
        if name in ctor_of and rng.get("name") in adts:
            return ctor_of[name]
        key = (name, json.dumps(ty, sort_keys=True))
        if dom:
            if key not in funcs:
                funcs[key] = z3.Function(name, *[sort_of(d) for d in dom], sort_of(rng))
                if (ax := legal_value_axiom(funcs[key], ty)) is not None:
                    background.append(ax)
            return funcs[key], len(dom)
        s = sort_of(rng)
        rname = rng.get("name")
        if (name, rname) in funcs:                     # an enumeration constant
            return funcs[(name, rname)], 0
        if key not in funcs:
            funcs[key] = z3.Const(name, s)
            if (ax := legal_value_axiom(funcs[key], ty)) is not None:
                background.append(ax)
        return funcs[key], 0

    # ---- generic fallback: the typed applicative encoding (as in Sledgehammer's HOL-to-first-order translation,
    # Meng and Paulson 2008). A function-typed value is an object of its own sort, applied through app_T; a lambda is
    # lifted to a new function with a defining axiom; a library constant without a fixed translation is an
    # uninterpreted symbol. Every HOL4 term gets a translation this way. Its models need not be standard HOL models,
    # so an answer "does not follow" that rests on such a statement is reported as unknown; "follows" and
    # "inconsistent" stay exact (fewer constraints can only make unsat harder).
    generic_ids, generic_heads, background, flushed = set(), set(), [], {}
    fn_sorts, app_fns, fvals, gfuncs = {}, {}, {}, {}
    def tykey(ty):
        return json.dumps(ty, sort_keys=True)
    def gsort(ty):
        if ty["kind"] == "type_application" and ty["name"] == "fun":
            k = tykey(ty)
            if k not in fn_sorts:
                fn_sorts[k] = z3.DeclareSort(f"Fn{len(fn_sorts)}")
                f, g = z3.Const(f"extf{len(fn_sorts)}", fn_sorts[k]), z3.Const(f"extg{len(fn_sorts)}", fn_sorts[k])
                x = z3.Const(f"extx{len(fn_sorts)}", gsort(ty["arguments"][0]))
                gx = wf(ty["arguments"][0], x)
                same = app(ty, f, x) == app(ty, g, x)
                background.append(z3.ForAll([f, g], z3.Implies(z3.ForAll([x], z3.Implies(gx, same) if gx is not None else same), f == g)))
            return fn_sorts[k]
        try:
            return sort_of(ty)
        except Untranslatable:
            k = "T_" + re.sub(r"\W+", "_", tykey(ty))[:60] + str(abs(hash(tykey(ty))) % 10**6)
            if k not in sorts:
                sorts[k] = z3.DeclareSort(k)
            return sorts[k]
    def app(ty, f, x):
        k = tykey(ty)
        if k not in app_fns:
            app_fns[k] = z3.Function(f"app{len(app_fns)}", gsort(ty), gsort(ty["arguments"][0]), gsort(ty["arguments"][1]))
        return app_fns[k](f, x)
    def apply_all(ty, f, xs):
        for x in xs:
            f = app(ty, f, x); ty = ty["arguments"][1]
        return f
    def gfunc(h):
        """a constant with no first-order translation (library, or taking functions): one uninterpreted symbol"""
        k = (h["name"], h.get("theory"), tykey(h["type"]))
        if k not in gfuncs:
            dom, rng = arrow(h["type"])
            nm = f"g_{h.get('theory')}_{h['name']}_{len(gfuncs)}"
            gfuncs[k] = (z3.Function(nm, *[gsort(d) for d in dom], gsort(rng)) if dom else z3.Const(nm, gsort(rng)), len(dom))
            if (ax := legal_value_axiom(gfuncs[k][0], h["type"])) is not None:
                background.append(ax)
        return gfuncs[k]
    def value_of(h, env):
        """the constant h as a first-class value of its function type, tied to its full application"""
        k = (h["name"], h.get("theory"), tykey(h["type"]))
        if k not in fvals:
            v = z3.Const(f"val_{h['name']}_{len(fvals)}", gsort(h["type"]))
            fvals[k] = v
            dom, _ = arrow(h["type"])
            names = [f"__bv{len(fvals)}_{i}" for i in range(len(dom))]
            xs = [z3.Const(n, gsort(d)) for n, d in zip(names, dom)]
            app_ast = h
            for n, d in zip(names, dom):
                app_ast = {"kind": "application", "function": app_ast, "argument": {"kind": "variable", "name": n, "type": d}}
            full = tr(app_ast, dict(zip(names, xs)), True)
            eq = apply_all(h["type"], v, xs) == full
            g = guarded(list(zip(xs, dom)))
            background.append(z3.ForAll(xs, z3.Implies(g, eq) if g is not None else eq) if xs else eq)
        return fvals[k]
    def type_of(t):
        """a term's HOL type (the exported abstraction nodes carry no type of their own)"""
        if "type" in t:
            return t["type"]
        if t["kind"] == "abstraction":
            return {"kind": "type_application", "theory": "min", "name": "fun",
                    "arguments": [t["variable"]["type"], type_of(t["body"])]}
        if t["kind"] == "application":
            return type_of(t["function"])["arguments"][1]
        raise Untranslatable("term without a type")
    def free_names(t, bound):
        if t["kind"] == "variable":
            return set() if t["name"] in bound else {t["name"]}
        if t["kind"] == "application":
            return free_names(t["function"], bound) | free_names(t["argument"], bound)
        if t["kind"] == "abstraction":
            return free_names(t["body"], bound | {t["variable"]["name"]})
        return set()
    def free_types(t, bound, acc):
        if t["kind"] == "variable" and t["name"] not in bound:
            acc.setdefault(t["name"], t["type"])
        elif t["kind"] == "application":
            free_types(t["function"], bound, acc); free_types(t["argument"], bound, acc)
        elif t["kind"] == "abstraction":
            free_types(t["body"], bound | {t["variable"]["name"]}, acc)
        return acc
    def lift(t, env):
        """lambda-lift: a new function of the bound variables in scope, with its defining axiom"""
        fv_types = free_types(t, set(), {})
        fv = sorted(n for n in free_names(t, set()) if n in env)
        args = [env[n] for n in fv]
        nm = f"lam{len(background)}_{uuid.uuid4().hex[:4]}"
        L = z3.Function(nm, *[a.sort() for a in args], gsort(type_of(t))) if args else z3.Const(nm, gsort(type_of(t)))
        val = L(*args) if args else L
        ys = [z3.Const(f"{n}_l{uuid.uuid4().hex[:4]}", a.sort()) for n, a in zip(fv, args)]
        lval = L(*ys) if ys else L
        x = z3.Const(t["variable"]["name"] + "_l" + uuid.uuid4().hex[:4], gsort(t["variable"]["type"]))
        inner = {**env, **dict(zip(fv, ys)), t["variable"]["name"]: x}
        body = tr(t["body"], inner, True)
        eq = app(type_of(t), lval, x) == body
        g = guarded([(y, fv_types[n]) for y, n in zip(ys, fv) if n in fv_types] + [(x, t["variable"]["type"])])
        background.append(z3.ForAll(ys + [x], z3.Implies(g, eq) if g is not None else eq))
        return val

    def tr(t, env, g=False):
        srt = gsort if g else sort_of
        if t["kind"] == "variable":
            if t["name"] in env:
                return env[t["name"]]
            if g:
                k = ("free", t["name"], tykey(t["type"]))
                if k not in gfuncs:
                    gfuncs[k] = (z3.Const(t["name"] + "_free", gsort(t["type"])), 0)
                return gfuncs[k][0]
            v, n = const(t["name"], t["type"])        # a free variable: an arbitrary fixed value
            if n:
                raise Untranslatable("free function variable")
            return v
        if t["kind"] == "abstraction":
            if g:
                return lift(t, env)
            raise Untranslatable("lambda")
        h, args = strip_comb(t)
        if h["kind"] == "abstraction":
            if g:
                return apply_all(type_of(h), lift(h, env), [tr(a, env, True) for a in args])
            raise Untranslatable("beta redex")
        if h["kind"] == "variable":
            if h["name"] in env:
                if g:
                    return apply_all(h["type"], env[h["name"]], [tr(a, env, True) for a in args])
                raise Untranslatable("higher-order variable")
            if g and arrow(h["type"])[0] and len(args) < len(arrow(h["type"])[0]):
                return apply_all(h["type"], tr(h, env, True), [tr(a, env, True) for a in args])
            try:
                f, n = const(h["name"], h["type"])
            except Untranslatable:
                if not g:
                    raise
                return apply_all(h["type"], tr(h, env, True), [tr(a, env, True) for a in args])
            return f(*[tr(a, env, g) for a in args]) if args else f
        name, thy = h["name"], h.get("theory")
        if name in ("!", "?", "?!") and thy == "bool" and len(args) == 1 and args[0]["kind"] == "abstraction":
            var = args[0]["variable"]
            if var["type"]["kind"] == "type_application" and var["type"]["name"] == "fun" and not g:
                raise Untranslatable("higher-order quantifier")
            x = z3.Const(var["name"] + "_" + uuid.uuid4().hex[:6], srt(var["type"]))
            body = tr(args[0]["body"], {**env, var["name"]: x}, g)
            gx = wf(var["type"], x)                     # legal values only (num >= 0, char < 256, ...)
            if name == "!":
                return z3.ForAll([x], z3.Implies(gx, body) if gx is not None else body)
            if name == "?":
                return z3.Exists([x], z3.And(gx, body) if gx is not None else body)
            y = z3.Const(var["name"] + "_u" + uuid.uuid4().hex[:6], srt(var["type"]))
            body_y = z3.substitute(body, (x, y))
            gy = wf(var["type"], y)
            inner = z3.Implies(z3.And(gy, body_y) if gy is not None else body_y, y == x)
            return z3.Exists([x], z3.And(*([gx] if gx is not None else []), body, z3.ForAll([y], inner)))
        if name == "T" and not args:
            return z3.BoolVal(True)
        if name == "F" and not args:
            return z3.BoolVal(False)
        if name in ("NUMERAL", "ZERO", "0", "BIT1", "BIT2"):
            return z3.IntVal(numeral(t))
        if thy == "list" and name == "NIL" and not args:
            return z3.Empty(srt(h["type"]))
        n_args = {"~": 1, "COND": 3, "real_of_num": 1, "real_neg": 1, "SUC": 1, "CHR": 1, "LENGTH": 1}.get(name, 2)
        key = (thy, name)
        if key in TABLE:
            if len(args) == n_args:
                a = [tr(x, env, g) for x in args]
                return TABLE[key](a)
            if not g:
                raise Untranslatable("partial application of " + name)
            return apply_all(h["type"], value_of(h, env), [tr(x, env, True) for x in args])
        if thy not in (ast["theory"],) and thy is not None:
            if not g:
                raise Untranslatable(f"library constant {thy}${name}")
            f, n = gfunc(h)
        else:
            try:
                f, n = const(name, h["type"])
            except Untranslatable:
                if not g:
                    raise
                f, n = gfunc(h)
        if n != len(args):
            if not g:
                raise Untranslatable("partial application of " + name)
            if len(args) < n:
                return apply_all(h["type"], value_of(h, env), [tr(x, env, True) for x in args])
            head = f(*[tr(x, env, True) for x in args[:n]])
            rest_ty = h["type"]
            for _ in range(n):
                rest_ty = rest_ty["arguments"][1]
            return apply_all(rest_ty, head, [tr(x, env, True) for x in args[n:]])
        a = [tr(x, env, g) for x in args]
        return f(*a) if a else f

    TABLE = {
        ("min", "="): lambda a: a[0] == a[1],
        ("min", "==>"): lambda a: z3.Implies(a[0], a[1]),
        ("bool", "/\\"): lambda a: z3.And(a[0], a[1]),
        ("bool", "\\/"): lambda a: z3.Or(a[0], a[1]),
        ("bool", "~"): lambda a: z3.Not(a[0]),
        ("bool", "COND"): lambda a: z3.If(a[0], a[1], a[2]),
        ("arithmetic", "+"): lambda a: a[0] + a[1],
        ("arithmetic", "-"): lambda a: z3.If(a[0] >= a[1], a[0] - a[1], 0),
        ("arithmetic", "*"): lambda a: a[0] * a[1],
        ("prim_rec", "<"): lambda a: a[0] < a[1],
        ("arithmetic", "<="): lambda a: a[0] <= a[1],
        ("arithmetic", ">"): lambda a: a[0] > a[1],
        ("arithmetic", ">="): lambda a: a[0] >= a[1],
        ("realax", "real_of_num"): lambda a: z3.ToReal(a[0]),
        ("realax", "/"): lambda a: z3.If(a[1] == 0, z3.RealVal(0), a[0] / a[1]),   # HOL4: x / 0 = 0
        ("arithmetic", "DIV"): lambda a: a[0] / a[1],
        ("arithmetic", "MOD"): lambda a: a[0] % a[1],
        ("num", "SUC"): lambda a: a[0] + 1,
        ("string", "CHR"): lambda a: a[0],
        ("list", "CONS"): lambda a: z3.Concat(z3.Unit(a[0]), a[1]),
        ("list", "APPEND"): lambda a: z3.Concat(a[0], a[1]),
        ("list", "LENGTH"): lambda a: z3.Length(a[0]),
        ("realax", "real_add"): lambda a: a[0] + a[1],
        ("realax", "real_mul"): lambda a: a[0] * a[1],
        ("realax", "real_neg"): lambda a: -a[0],
        ("realax", "real_lt"): lambda a: a[0] < a[1],
        ("realax", "real_sub"): lambda a: a[0] - a[1],
        ("real", "real_sub"): lambda a: a[0] - a[1],
        ("real", "real_lte"): lambda a: a[0] <= a[1],
        ("real", "real_gt"): lambda a: a[0] > a[1],
        ("real", "real_ge"): lambda a: a[0] >= a[1],
        ("real", "/"): lambda a: z3.If(a[1] == 0, z3.RealVal(0), a[0] / a[1]),
        ("real", "real_div"): lambda a: z3.If(a[1] == 0, z3.RealVal(0), a[0] / a[1]),
    }

    def translate(term):
        try:
            return tr(term, {}), None
        except (Untranslatable, z3.Z3Exception) as e:
            first = str(e)
        try:
            f = tr(term, {}, True)                      # the generic fallback
            generic_ids.add(f.get_id())
            return f, None
        except (Untranslatable, z3.Z3Exception, KeyError, IndexError, TypeError) as e:
            return None, f"{first}; generic encoding failed: {e}"

    def split_imp(t):
        h, args = strip_comb(t)
        if h["kind"] == "constant" and h["name"] == "==>" and len(args) == 2:
            return args[0], args[1]
        return None, t

    def conjuncts(t):
        h, args = strip_comb(t)
        if h["kind"] == "constant" and h["name"] == "/\\" and len(args) == 2:
            return conjuncts(args[0]) + conjuncts(args[1])
        return [t]

    def strip_forall(t):
        vs = []
        while True:
            h, args = strip_comb(t)
            if h["kind"] == "constant" and h["name"] == "!" and len(args) == 1 and args[0]["kind"] == "abstraction":
                vs.append(args[0]["variable"]); t = args[0]["body"]
            else:
                return vs, t

    every = {t["name"]: t for t in ast["theorem_values"] + ast["theorems"] + ast["definitions"]}
    if "final" not in every:                            # prompts before v10 did not ask for a theorem named final
        raise SystemExit("no theorem named final; this engine checks the conclusions of final")
    final = every["final"]["conclusion"]
    fvars, fbody = strip_forall(final)
    # outer variables of final: proving !x. A x ==> C x is proving A c ==> C c for an arbitrary fixed c, so each one
    # becomes a constant of its type (named after the variable) and the rest goes on as for a closed final
    def fix(t, names):
        if t["kind"] == "variable" and t["name"] in names:
            return {"kind": "constant", "theory": ast["theory"], "name": t["name"], "type": t["type"]}
        if t["kind"] == "application":
            return {**t, "function": fix(t["function"], names), "argument": fix(t["argument"], names)}
        if t["kind"] == "abstraction":
            inner = names - {t["variable"]["name"]}
            return {**t, "body": fix(t["body"], inner)}
        return t
    if fvars:
        fbody = fix(fbody, {v["name"] for v in fvars})
    ant, con = split_imp(fbody)
    stated = conjuncts(ant) if ant is not None else []
    starts = [("premise " + str(i + 1), p) for i, p in enumerate(stated)] + [("axiom " + ax["name"], ax["conclusion"]) for ax in ast["axioms"]]
    # theorems HOL4 makes for an enumerated datatype (move_TY_DEF, move_CASE, ...) are what the Z3 enumeration already says
    defs = [(d["name"], d["conclusion"]) for d in ast["definitions"]
            if not any(d["name"].startswith(ty + "_") for ty in list(enums) + list(adts))
            and not re.search(r"_(TY_DEF|case_def|size_def|repfns|bijections)$", d["name"])]   # HOL4's datatype internals
    # Library definitions exported by HOL4 (export_hol4_terms.sml), for library constants that have no fixed
    # translation above: each is instantiated at every type the argument uses the constant at (monomorphisation,
    # as Sledgehammer does), and joins the definitions as background.
    native = {k for k in TABLE} | {("arithmetic", n) for n in ("NUMERAL", "ZERO", "BIT1", "BIT2", "ALT_ZERO")} \
             | {("num", "0"), ("num", "SUC"), ("list", "NIL")}
    def lhs_heads(t):
        heads = []
        for cj in conjuncts(strip_forall(t)[1]):
            h, args = strip_comb(strip_forall(cj)[1])
            if h["kind"] == "constant" and h["name"] == "=" and len(args) == 2:
                lh = strip_comb(args[0])[0]
                if lh["kind"] == "constant":
                    heads.append(lh)
        return heads
    def tyvars_in(ty):
        if ty["kind"] != "type_application":
            return {ty.get("name")}
        return set().union(*[tyvars_in(a) for a in ty["arguments"]]) if ty["arguments"] else set()
    def match_ty(gen, inst, sub):
        if gen["kind"] != "type_application":
            k = gen.get("name")
            if k in sub and sub[k] != inst:
                return None
            sub[k] = inst; return sub
        if inst["kind"] != "type_application" or gen["name"] != inst["name"] or len(gen["arguments"]) != len(inst["arguments"]):
            return None
        for g, i in zip(gen["arguments"], inst["arguments"]):
            if match_ty(g, i, sub) is None:
                return None
        return sub
    def subst_ty(ty, sub):
        if ty["kind"] != "type_application":
            return sub.get(ty.get("name"), ty)
        return {**ty, "arguments": [subst_ty(a, sub) for a in ty["arguments"]]}
    def subst_term(t, sub):
        if t["kind"] in ("variable", "constant"):
            return {**t, "type": subst_ty(t["type"], sub)}
        if t["kind"] == "application":
            return {**t, "function": subst_term(t["function"], sub), "argument": subst_term(t["argument"], sub)}
        if t["kind"] == "abstraction":
            return {**t, "variable": subst_term(t["variable"], sub), "body": subst_term(t["body"], sub)}
        return t
    def lib_uses(terms):
        found = {}
        for t in terms:
            stack = [t]
            while stack:
                x = stack.pop()
                if x["kind"] == "application":
                    stack += [x["function"], x["argument"]]
                elif x["kind"] == "abstraction":
                    stack.append(x["body"])
                elif x["kind"] == "constant" and x.get("theory") not in (ast["theory"], "bool", "min", None) \
                        and (x["theory"], x["name"]) not in native:
                    found.setdefault((x["theory"], x["name"]), {})[json.dumps(x["type"], sort_keys=True)] = x["type"]
        return found
    # The argument's own polymorphic definitions are instantiated the same way. A definition that leaves a type open
    # (rule s <=> P with s unused in P, which HOL4 types 'a -> bool) would otherwise define a symbol over a sort of
    # its own, a different symbol from the rule the premises use at eventuality -> bool, and "does not follow" would
    # be wrong (GPT g16_02, 2026-10-21).
    def own_uses(terms):
        found = {}
        for t in terms:
            stack = [t]
            while stack:
                x = stack.pop()
                if x["kind"] == "application":
                    stack += [x["function"], x["argument"]]
                elif x["kind"] == "abstraction":
                    stack.append(x["body"])
                elif x["kind"] == "constant" and x.get("theory") == ast["theory"] and not tyvars_in(x["type"]):
                    found.setdefault(x["name"], {})[json.dumps(x["type"], sort_keys=True)] = x["type"]
        return found
    poly = {n: [h for h in lhs_heads(d) if h.get("theory") == ast["theory"] and tyvars_in(h["type"])] for n, d in defs}
    poly = {n: hs for n, hs in poly.items() if hs}
    if poly:
        mono = [(n, d) for n, d in defs if n not in poly]
        own_instances, seen_inst = [], set()
        while len(own_instances) < 300:
            uses_own = own_uses([p for _, p in starts] + [final] + [d for _, d in mono + own_instances])
            new = []
            for n, d in defs:
                for h in poly.get(n, []):
                    for ty in uses_own.get(h["name"], {}).values():
                        sub = match_ty(h["type"], ty, {})
                        k = (n, json.dumps(sub, sort_keys=True))
                        if sub is None or k in seen_inst:
                            continue
                        seen_inst.add(k)
                        new.append((n + " at " + ", ".join(f"{v}={w.get('name')}" for v, w in sub.items()), subst_term(d, sub)))
            if not new:
                break
            own_instances += new
        defs = mono + own_instances + [(n, d) for n, d in defs if n in poly and not any(k[0] == n for k in seen_inst)]
    internal = re.compile(r"ISO|_REP|REP_|repfns|BIJ|_size|ind_type|^num\$|recspace")
    libdefs = [d for d in ast.get("library_definitions", []) if not internal.search(d["name"])]
    # a library's own axioms (none for HOL4's definitional theories) join the background, at the types used
    for d in ast.get("library_axioms", []):
        lib_ax_uses = lib_uses([d["conclusion"]])
        free_tv = set()
        stack = [d["conclusion"]]
        while stack:
            x = stack.pop()
            if x["kind"] in ("variable", "constant"):
                free_tv |= tyvars_in(x["type"])
            elif x["kind"] == "application":
                stack += [x["function"], x["argument"]]
            elif x["kind"] == "abstraction":
                stack += [x["variable"], x["body"]]
        if not free_tv:
            defs.append(("library axiom " + d["name"], d["conclusion"]))
    by_head = {}
    for d in libdefs:
        for h in lhs_heads(d["conclusion"]):
            if (h["theory"], h["name"]) not in native:
                by_head.setdefault((h["theory"], h["name"]), []).append((d, h))
    uses = lib_uses([p for _, p in starts] + [d for _, d in defs] + [final])
    done, pending, lib_instances = set(), list(uses.items()), []
    while pending and len(lib_instances) < 300:
        (key, types) = pending.pop()
        for tyj, ty in types.items():
            for d, h in by_head.get(key, []):
                sub = match_ty(h["type"], ty, {}) if tyvars_in(h["type"]) else {}
                if sub is None:
                    continue
                inst = subst_term(d["conclusion"], sub) if sub else d["conclusion"]
                k = (d["name"], json.dumps(sub, sort_keys=True))
                if k in done:
                    continue
                done.add(k)
                lib_instances.append(("library " + d["name"], inst))
                pending += list(lib_uses([inst]).items())
    defs = defs + lib_instances
    out = {"starts": [n for n, _ in starts], "untranslatable": [], "conclusions": []}
    generic_def_names, name_cache = set(), {}
    def names_of(f):
        """the uninterpreted symbols a formula mentions"""
        k = f.get_id()
        if k in name_cache:
            return name_cache[k]
        found, stack, seen = set(), [f], set()
        while stack:
            e = stack.pop()
            if e.get_id() in seen:
                continue
            seen.add(e.get_id())
            if z3.is_quantifier(e):
                stack.append(e.body()); continue
            if z3.is_app(e):
                if e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                    found.add(e.decl().name())
                stack.extend(e.children())
        name_cache[k] = found
        return found
    def involves_generic(forms):
        """does a question rest on a statement that only the generic encoding could translate?"""
        for f in forms:
            if f is None:
                continue
            if f.get_id() in generic_ids or (generic_def_names and names_of(f) & generic_def_names):
                return True
        return False
    def flush(s):
        """add the generic encoding's background axioms made since the last call (lifted lambdas, bridges)"""
        k = id(s); n = flushed.get(k, 0)
        if n < len(background):
            s.add(*background[n:]); flushed[k] = len(background)

    # Countermodels are checked in HOL semantics before "does not" is answered (hol_semantics.py): the original HOL
    # starting points must come out true and the conclusion false in an interpretation built from Z3's model, with
    # every defined constant evaluated by its own definition. A countermodel that does not pass is a candidate only,
    # and the answer is unknown, as Nitpick reports a potential counterexample.
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from hol_semantics import Interp, Semantics, definition_clauses
    constructor_names = {c for cs in enums.values() for c in cs} | {c for alts in adts.values() for c, _ in alts}
    clauses = definition_clauses(ast["definitions"] + libdefs, ast["theory"], constructor_names)
    lib_axiom_terms = [d for n, d in defs if n.startswith("library axiom ")]
    def symbol(key):
        f = funcs.get(key)
        return None if f is None else (f, len(arrow(json.loads(key[1]))[0]))
    class EnumValues(dict):
        def __missing__(self, key):
            sort_of({"kind": "type_application", "name": key[1], "arguments": []})
            return funcs[key]
    enum_values = EnumValues()
    semantics = Semantics(ast["theory"], symbol, sort_of, enums, adts, {}, enum_values, clauses,
                          lambda: [(k, f) for k, f in list(funcs.items())
                                   if isinstance(k[1], str) and k[1].startswith("{") and not z3.is_const(f)])
    countermodels, failures = {"validated": 0, "not validated": 0}, {}
    def interp_for(model):
        make_adts()
        for f in list(funcs.values()):                  # name every element the model's constants stand for
            if z3.is_const(f) and f.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
                model.eval(f, model_completion=True)
        semantics.ctor_z3 = {c: v[0] for c, v in ctor_of.items()}
        return Interp(semantics, model)
    def holds_up(I, true_terms, false_terms):
        """in the interpretation I, do true_terms hold and false_terms fail (and the library axioms hold)?"""
        try:
            ok, why = True, None
            for t, want in [(t, True) for t in list(true_terms) + lib_axiom_terms] + [(t, False) for t in false_terms]:
                v = I.evb(t)
                if v is not want:
                    ok, why = False, f"{'unknown' if v is None else v}: {I.why or ''}"
                    break
        except Exception as e:
            ok, why = False, f"error: {e}"
        countermodels["validated" if ok else "not validated"] += 1
        if not ok:
            failures[why] = failures.get(why, 0) + 1
        return ok
    def genuine(model, true_terms, false_terms):
        """does the Z3 model give a HOL interpretation where true_terms hold and false_terms fail?"""
        try:
            I = interp_for(model)
        except Exception as e:
            countermodels["not validated"] += 1
            failures[f"error: {e}"] = failures.get(f"error: {e}", 0) + 1
            return False
        return holds_up(I, true_terms, false_terms)
    # Checked countermodels are kept: each with every starting point true in it and every conclusion false in it.
    # A later question any of them answers needs no solver call, and MARCO grows a satisfiable set by the starting
    # points the model already satisfies (as cpmpy's MARCO does after Liffiton et al. 2016).
    held = []
    def keep(I):
        ts = frozenset(i for i in kept if I.evb(starts[i][1]) is True)
        fg = frozenset(g for g, t in list(goal_hol.items()) if I.evb(t) is False)
        held.append((ts, fg))
        return ts
    def known(ids, goal_switch):
        need, gid = set(ids), (goal_switch.get_id() if goal_switch is not None else None)
        for ts, fg in held:
            if need <= ts and (gid is None or gid in fg):
                return ts
        return None
    def checked(model, ids, true_terms, false_terms):
        """the starting points true in the model if it holds up as a countermodel, else None"""
        try:
            I = interp_for(model)
        except Exception as e:
            countermodels["not validated"] += 1
            failures[f"error: {e}"] = failures.get(f"error: {e}", 0) + 1
            return None
        return keep(I) | frozenset(ids) if holds_up(I, true_terms, false_terms) else None

    solver = z3.Solver()
    solver.set("timeout", time_ms)
    def_fs = []
    for n, d in defs:
        f, err = translate(d)
        if err:
            out["untranslatable"].append([n, err])
        else:
            solver.add(f); def_fs.append(f)
            if f.get_id() in generic_ids:
                out.setdefault("generic", []).append(n)
                generic_def_names.update(names_of(f))
    switch, kept, start_formula, goal_formula = {}, [], {}, {}
    for i, (n, p) in enumerate(starts):
        f, err = translate(p)
        if err:
            out["untranslatable"].append([n, err]); continue
        if f.get_id() in generic_ids:
            out.setdefault("generic", []).append(n)
        b = z3.Bool(f"start_{i}")
        solver.add(z3.Implies(b, f)); switch[i] = b; kept.append(i); start_formula[i] = f

    # A countermodel is first looked for in a small finite domain: each uninterpreted sort holds only its named
    # constants and two more things. A model found there is a real countermodel, so "does not" stays exact; when none
    # is found the unrestricted question is asked. With function symbols such as OrC : ev -> ev -> ev, Z3's own search
    # for a countermodel can wander through ever larger models until the time limit.
    extra = {}
    def closure(k=2):
        dom = {}
        for v in list(funcs.values()):
            if z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED and v.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
                dom.setdefault(v.sort().name(), (v.sort(), []))[1].append(v)
        ax = []
        for name, (srt, cs) in dom.items():
            fresh = extra.setdefault(name, [z3.Const(f"{name}__extra{i}", srt) for i in range(k)])
            x = z3.Const(f"{name}__dom", srt)
            ax.append(z3.ForAll([x], z3.Or([x == c for c in cs + fresh])))
        return ax
    unknown_why = {"time budget": 0, "solver gave up": 0, "rests on the generic encoding": 0,
                   "countermodel not validated": 0}
    goal_hol = {}                                       # goal switch -> the HOL statement it asks about
    def out_of_time():
        if time.time() > deadline:
            limits["budget"] = True
            return True
        return False
    def bounded_sat(s, assumptions=(), involved=False):
        """a model in the small finite domain, or None"""
        if out_of_time() or involved:                   # a finite model of the generic encoding may not be a HOL model
            return None
        s.push(); s.add(*closure()); r = s.check(*assumptions) if assumptions else s.check()
        m = s.model() if r == z3.sat else None
        s.pop()
        return m

    def ask(ids, goal_switch):
        """follows / does not / unknown for the starting points ids and the conclusion behind goal_switch; with
        "follows" the unsat core, with "does not" every starting point true in the countermodel"""
        hit = known(ids, goal_switch)
        if hit is not None:
            return "does not", hit
        assum = [switch[i] for i in ids] + ([goal_switch] if goal_switch is not None else [])
        flush(solver)
        involved = involves_generic([start_formula.get(i) for i in ids] +
                                    ([goal_formula.get(goal_switch.get_id())] if goal_switch is not None else []))
        hol_true = [starts[i][1] for i in ids]
        hol_false = [goal_hol[goal_switch.get_id()]] if goal_switch is not None else []
        m = bounded_sat(solver, [assum], involved)
        if m is not None and (ts := checked(m, ids, hol_true, hol_false)) is not None:
            return "does not", ts
        if out_of_time():
            unknown_why["time budget"] += 1
            return "unknown", None
        r = solver.check(assum)
        if r == z3.unsat:
            core = [i for i in ids if any(z3.eq(c, switch[i]) for c in solver.unsat_core())]
            return "follows", core
        if r == z3.sat:
            if involved:
                unknown_why["rests on the generic encoding"] += 1
                return "unknown", None
            if (ts := checked(solver.model(), ids, hol_true, hol_false)) is not None:
                return "does not", ts
            unknown_why["countermodel not validated"] += 1
            return "unknown", None
        unknown_why["solver gave up"] += 1
        return "unknown", None

    def nonneg_axioms():
        """every num-valued constant and function value is at least 0 (HOL's num), as background facts"""
        ax = []
        for key, f in list(funcs.items()):
            if not (isinstance(key, tuple) and len(key) == 2 and isinstance(key[1], str) and key[1].startswith("{")):
                continue
            ty = json.loads(key[1]); dom, rng = arrow(ty)
            if rng.get("name") != "num":
                continue
            if not dom:
                ax.append(f >= 0)
            else:
                vs = [z3.Const(f"nn{k}_" + uuid.uuid4().hex[:4], sort_of(d)) for k, d in enumerate(dom)]
                ax.append(z3.ForAll(vs, f(*vs) >= 0))
        return ax
    flush(solver)                                       # legal-value axioms and the generic encoding's background
    # consistency of everything
    r, core = ask(kept, None)
    out["consistent"] = {"follows": "inconsistent", "does not": "consistent", "unknown": "unknown"}[r]
    if r == "follows":
        # a smallest contradictory set: shrink the core
        c = list(core)
        for i in list(c):
            if i not in c:
                continue
            rest = [j for j in c if j != i]
            rr, core2 = ask(rest, None)
            if rr == "follows":                          # shrink to the new core (clause-set refinement)
                c = [j for j in rest if j in set(core2)]
        out["contradiction"] = [starts[i][0] for i in c]

    def marco(goal_switch):
        """every smallest set of starting points that gives the conclusion (MARCO over the switches)"""
        mp = z3.Solver()
        idx = {i: z3.Bool(f"m_{i}") for i in kept}
        mus, complete, unknowns, steps = [], True, 0, 0
        while mp.check() == z3.sat:
            steps += 1
            if steps > marco_cap or out_of_time():         # MARCO ends on its own, but the number of steps can grow
                limits["marco"] = limits["marco"] or steps > marco_cap   # exponentially with the starting points
                complete = False
                break
            m = mp.model()
            seed = [i for i in kept if not z3.is_false(m.eval(idx[i], model_completion=False))]
            r, core = ask(seed, goal_switch)
            if r == "does not":
                grow = [i for i in kept if i in core]  # grow by the model: every starting point true in it
                for i in kept:                         # then to a largest set that does not give the conclusion
                    if i not in grow:
                        rr, ts = ask(grow + [i], goal_switch)
                        if rr == "does not":
                            grow = [j for j in kept if j in ts]
                rest = [idx[i] for i in kept if i not in grow]
                mp.add(z3.Or(rest) if rest else z3.BoolVal(False))
            elif r == "follows":
                c = list(core)
                for i in list(c):                      # shrink to a smallest set
                    if i not in c:
                        continue
                    rest = [j for j in c if j != i]
                    rr, core2 = ask(rest, goal_switch)
                    if rr == "follows":                # shrink to the new core (clause-set refinement)
                        c = [j for j in rest if j in set(core2)]
                    elif rr == "unknown":
                        complete = False
                mus.append(sorted(c))
                mp.add(z3.Or([z3.Not(idx[i]) for i in c]) if c else z3.BoolVal(False))
                if len(mus) >= support_cap:            # with many interchangeable starting points the smallest
                    limits["supports"] = True          # supports can run into thousands; the first ones are kept
                    complete = False
                    break
            else:
                complete = False; unknowns += 1
                mp.add(z3.Or([z3.Not(idx[i]) for i in seed]) if seed else z3.BoolVal(False))
                if unknowns > 20:
                    break
        return mus, complete

    mus_of, goal_of, goal_hol_of = {}, {}, {}
    for j, c in enumerate(conjuncts(con), 1):
        f, err = translate(c)
        rec = {"j": j, "untranslatable": err}
        if err is None:
            g = z3.Bool(f"goal_{j}")
            solver.add(z3.Implies(g, z3.Not(f))); goal_formula[g.get_id()] = f; goal_hol[g.get_id()] = c
            r, _ = ask(kept, g)
            rec["follows_from_all"] = r
            if r == "follows":
                mus, complete = marco(g)
                rec["supports"] = [[starts[i][0] for i in m] for m in mus]
                rec["complete"] = complete
                mus_of[j], goal_of[j], goal_hol_of[j] = mus, f, c
        out["conclusions"].append(rec)
    start_f = {}
    for i, (n, p) in enumerate(starts):
        if i in switch:
            start_f[i] = translate(p)[0]
    # Every-position test. A place is argument k of a declared predicate P; it is tested wherever a constant e of an
    # uninterpreted sort fills it in a starting point. Inside each smallest support M of a conclusion C, the facts with
    # e at P's place k are changed:
    #   drop   P at those places is renamed to a fresh symbol (the facts are gone)
    #   any    e at those places is replaced by a fresh constant u about which nothing is known
    #   co     as any, plus u != e and T(u) = T(e) for every truth predicate T of e's sort
    # A truth predicate of a sort is a predicate T used in a truth bridge T(x) = phi (phi not mentioning x); its own
    # place is the truth bridge and is not tested. A sort with no truth predicate gets drop and any only. Results:
    #   not needed         C follows after drop
    #   gives the truth    C follows after drop once the truth values that M fixes for the things in the dropped
    #                      facts are added: the facts served only to give a truth, as knowing something gives its truth
    #   anything there     C follows after any: what fills the place does not matter            (transparent)
    #   truth value only   C follows after co: only the truth value of what fills it matters     (transparent)
    #   which one matters  Z3 finds a countermodel after co                                      (opaque)
    #   pinned             the other starting points force u = e, so nothing else can stand there
    # Each occurrence is changed alone, so renaming e everywhere it stands never counts as a replacement.
    theory = ast["theory"]
    def own(t):
        return t["kind"] == "constant" and t.get("theory") == theory
    def usort(ty):
        if ty["kind"] == "type_application" and not ty["arguments"] and ty["name"] not in ("bool", "num", "fun") \
                and ty["name"] not in enums:
            return ty["name"]
        return None
    def rebuild(h, args):
        for a in args:
            h = {"kind": "application", "function": h, "argument": a}
        return h
    def walk(t):
        yield t
        if t["kind"] == "application":
            yield from walk(t["function"]); yield from walk(t["argument"])
        elif t["kind"] == "abstraction":
            yield from walk(t["body"])
    def mentions_ast(t, x):
        return any(s["kind"] == x["kind"] and s["name"] == x["name"] for s in walk(t) if s["kind"] in ("constant", "variable"))
    # in a bridge whose both sides are single atoms (True p = Unlawful c), the truth predicate is the side whose
    # predicate stands in more bridges: a truth predicate applies to many contents
    bridges = []
    for _, term in starts + defs:
        for s in walk(term):
            if s["kind"] != "application":
                continue
            h, args = strip_comb(s)
            if not (h["kind"] == "constant" and h["name"] == "=" and len(args) == 2 and arrow(h["type"])[0][0].get("name") == "bool"):
                continue
            sides = []
            for side, other in ((args[0], args[1]), (args[1], args[0])):
                sh, sa = strip_comb(side)
                if own(sh) and len(sa) == 1 and sa[0]["kind"] in ("constant", "variable") and usort(sa[0]["type"]) \
                        and not mentions_ast(other, sa[0]):
                    sides.append((sh["name"], sh["type"], usort(sa[0]["type"])))
            if sides:
                bridges.append(sides)
    count = {}
    for sides in bridges:
        for n, _, _ in sides:
            count[n] = count.get(n, 0) + 1
    truth = {}                                          # sort -> {truth predicate: its type}
    for sides in bridges:
        top = max(count[n] for n, _, _ in sides)
        for n, ty, srt in sides:
            if count[n] == top:
                truth.setdefault(srt, {})[n] = ty
    untested = set()
    def places(term):
        """(pred, k, e, type) -> how many times e fills place k of pred in term (whole applications only)"""
        found = {}
        def visit(t):
            if t["kind"] == "abstraction":
                visit(t["body"]); return
            if t["kind"] != "application":
                return
            h, args = strip_comb(t)
            if h["kind"] == "abstraction":
                visit(h)
            for a in args:
                visit(a)
            if own(h):
                for k, a in enumerate(args):
                    if own(a) and usort(a["type"]):
                        if usort(a["type"]) not in truth:
                            untested.add(usort(a["type"]))
                        if h["name"] not in truth.get(usort(a["type"]), {}):
                            key = (h["name"], k, a["name"], json.dumps(a["type"], sort_keys=True))
                            found[key] = found.get(key, 0) + 1
        visit(term)
        return found
    def fillers(terms, pred, k, e):
        """the constants with a truth predicate in the facts where e fills place k of pred"""
        found = set()
        for term in terms:
            for s in walk(term):
                if s["kind"] != "application":
                    continue
                h, args = strip_comb(s)
                if own(h) and h["name"] == pred and k < len(args) and own(args[k]) and args[k]["name"] == e:
                    found |= {(a["name"], json.dumps(a["type"], sort_keys=True)) for a in args
                              if own(a) and usort(a["type"])}
        return found
    def change(t, pred, k, e, new, n, seen=None):
        """at the n-th place where e fills place k of pred (counted as places() counts): new None renames pred
        there (drop); otherwise new stands in place of e there"""
        seen = seen if seen is not None else [0]
        if t["kind"] == "abstraction":
            return {**t, "body": change(t["body"], pred, k, e, new, n, seen)}
        if t["kind"] != "application":
            return t
        h, args = strip_comb(t)
        if h["kind"] == "abstraction":
            h = change(h, pred, k, e, new, n, seen)
        args = [change(a, pred, k, e, new, n, seen) for a in args]
        if own(h) and h["name"] == pred and k < len(args) and own(args[k]) and args[k]["name"] == e:
            if seen[0] == n:
                if new is None:
                    h = {**h, "name": pred + "__drop"}
                else:
                    args = args[:k] + [new] + args[k + 1:]
            seen[0] += 1
        return rebuild(h, args)
    # HOL terms built here, for questions whose answer "no" is used and so must be checked in HOL semantics
    BOOLT = {"kind": "type_application", "theory": "min", "name": "bool", "arguments": []}
    def funty(a, b):
        return {"kind": "type_application", "theory": "min", "name": "fun", "arguments": [a, b]}
    def h_const(name, ty):
        return {"kind": "constant", "theory": theory, "name": name, "type": ty}
    def h_app(f, *xs):
        for x in xs:
            f = {"kind": "application", "function": f, "argument": x}
        return f
    def h_eq(a, b):
        ty = type_of(a)
        return h_app({"kind": "constant", "theory": "min", "name": "=", "type": funty(ty, funty(ty, BOOLT))}, a, b)
    def h_neg(a):
        return h_app({"kind": "constant", "theory": "bool", "name": "~", "type": funty(BOOLT, BOOLT)}, a)
    H_FALSE = {"kind": "constant", "theory": "bool", "name": "F", "type": BOOLT}
    zs = z3.Solver(); zs.set("timeout", time_ms)
    zs.add(*def_fs)
    def entails(forms, goal, hol=None):
        """yes / no / unknown. hol = (HOL terms of forms, HOL term of goal) when the caller uses the answer "no":
        then "no" needs a countermodel that holds up in HOL semantics. Without hol only "yes" is meaningful."""
        if out_of_time():
            unknown_why["time budget"] += 1
            return "unknown"
        flush(zs)
        involved = involves_generic(list(forms) + [goal])
        zs.push(); zs.add(*forms); zs.add(z3.Not(goal))
        m = bounded_sat(zs, (), involved)
        if m is not None and (hol is None or genuine(m, hol[0], [hol[1]])):
            zs.pop()
            return "no"
        r = z3.unknown if out_of_time() else zs.check()
        m = zs.model() if r == z3.sat else None
        zs.pop()
        if r == z3.sat and involved:
            unknown_why["rests on the generic encoding"] += 1
            return "unknown"
        if r == z3.sat and hol is not None and not genuine(m, hol[0], [hol[1]]):
            unknown_why["countermodel not validated"] += 1
            return "unknown"
        if r not in (z3.sat, z3.unsat):
            unknown_why["time budget" if out_of_time() else "solver gave up"] += 1
        return "yes" if r == z3.unsat else "no" if r == z3.sat else "unknown"
    results, fixed = {}, {}
    for j, mus in mus_of.items():
        goal, goal_h = goal_of[j], goal_hol_of[j]
        if len(mus) > 5:
            out.setdefault("positions_supports_tested", {})[j] = [5, len(mus)]
        for si, m in enumerate(mus[:5], 1):
            terms = [starts[i][1] for i in m]
            forms = [start_f[i] for i in m]
            occ = []                                   # (pred, k, e, type, term index, n)
            for ti, t in enumerate(terms):
                for key, cnt in sorted(places(t).items()):
                    occ += [key + (ti, n) for n in range(cnt)]
            for pred, k, e, tyj, ti, n in occ:
                one = lambda new: [change(t, pred, k, e, new, n) if i == ti else t for i, t in enumerate(terms)]
                ety = json.loads(tyj)
                ez = const(e, ety)[0]
                Ts = [const(P, ty)[0] for P, ty in truth.get(usort(ety), {}).items()]
                drop_f = [translate(t)[0] for t in one(None)]
                r = entails(drop_f, goal, (one(None), goal_h))
                if r != "no":
                    status = "not needed" if r == "yes" else "unknown"
                else:
                    lits, lits_h = [], []
                    for x, xty in sorted(fillers([terms[ti]], pred, k, e)):
                        xz = const(x, json.loads(xty))[0]
                        for P, ty in truth.get(usort(json.loads(xty)), {}).items():
                            T = const(P, ty)[0]
                            key = (tuple(m), x, P)
                            if key not in fixed:
                                th = h_app(h_const(P, ty), h_const(x, json.loads(xty)))
                                fixed[key] = (T(xz), th) if entails(forms, T(xz)) == "yes" else \
                                    (z3.Not(T(xz)), h_neg(th)) if entails(forms, z3.Not(T(xz))) == "yes" else None
                            if fixed[key] is not None:
                                lits.append(fixed[key][0]); lits_h.append(fixed[key][1])
                    r = entails(drop_f + lits, goal, (one(None) + lits_h, goal_h)) if lits else "no"
                    if r != "no":
                        status = "gives the truth" if r == "yes" else "unknown"
                    else:
                        u = {"kind": "constant", "theory": theory, "name": e + "__any", "type": ety}
                        uz = const(e + "__any", ety)[0]
                        any_f = [translate(t)[0] for t in one(u)] + [uz != ez]
                        any_h = one(u) + [h_neg(h_eq(u, h_const(e, ety)))]
                        r = entails(any_f, z3.BoolVal(False), (any_h, H_FALSE))
                        if r == "yes":                  # the other starting points force u = e: nothing else can stand there
                            status = "pinned"
                        elif r == "unknown":
                            status = "unknown"
                        elif (r := entails(any_f, goal, (any_h, goal_h))) == "yes":
                            status = "anything there"
                        elif not Ts:                    # no truth predicate: nothing to share with e
                            status = {"no": "which one matters", "unknown": "unknown"}[r]
                        else:
                            same_h = [h_eq(h_app(h_const(P, ty), u), h_app(h_const(P, ty), h_const(e, ety)))
                                      for P, ty in truth.get(usort(ety), {}).items()]
                            r = entails(any_f + [T(uz) == T(ez) for T in Ts], goal, (any_h + same_h, goal_h))
                            status = {"yes": "truth value only", "no": "which one matters", "unknown": "unknown"}[r]
                results.setdefault((pred, k), []).append({"conclusion": j, "support": si, "filler": e, "status": status})
    flags = ("anything there", "truth value only")
    def verdict(rs):
        ss = {x["status"] for x in rs}
        if ss & set(flags):
            return "transparent"
        if "unknown" in ss:
            return "unknown"
        if "which one matters" in ss:
            return "opaque"
        if "gives the truth" in ss:
            return "gives the truth only"
        if "pinned" in ss:
            return "pinned"
        return "not needed"
    out["truth_predicates"] = {s: sorted(ps) for s, ps in truth.items()}
    out["untested_sorts"] = sorted(untested)
    out["positions"] = [{"predicate": p, "argument": k + 1, "verdict": verdict(rs), "results": rs}
                        for (p, k), rs in sorted(results.items())]
    # Misused logic (a hard flaw, the user 2026-10-20: "算硬伤吧"): a declared constant with no definition that takes a
    # truth value. In every model it is one of the few truth functions of its arguments, so it cannot say "ought",
    # "knows", "possibly" or "because"; whatever its name, two statements with the same truth value become the same
    # to it. A defined truth function (like a defined negation) is fine.
    defined = set()
    for d in ast["definitions"]:
        for c in conjuncts(strip_forall(d["conclusion"])[1]):
            h, args = strip_comb(strip_forall(c)[1])
            if h["kind"] == "constant" and h["name"] == "=" and args:
                lh = strip_comb(args[0])[0]
                if lh["kind"] == "constant":
                    defined.add(lh["name"])
    takes_bool = set()
    for t in [x["conclusion"] for x in ast["axioms"] + ast["definitions"] + ast["theorems"] + ast["theorem_values"]]:
        for s in walk(t):
            if own(s) and any(d["kind"] == "type_application" and d["name"] == "bool" for d in arrow(s["type"])[0]):
                takes_bool.add(s["name"])
    # constructors of declared datatypes and records, and HOL4's own record and case constants, are not operators
    constructors = set()
    for body in [m.group(1) or m.group(2) for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S)]:
        for decl in re.split(r";\s*(?=\w+\s*=)|\n(?=\s*\w+\s*=)", body):
            if "=" in decl and "<|" not in decl:
                constructors |= {alt.split()[0] for alt in decl.split("=", 1)[1].split("|") if alt.split()}
    internal = {n for n in takes_bool if "." in n or n.endswith(("_fupd", "_CASE", "_size")) or n in constructors}
    out["takes_truth_value"] = sorted(takes_bool - defined - internal)
    # The final conclusion asserted rather than proved (begging the question): a theorem named final that is an
    # axiom, so HOL4 checked no step to it (DeepSeek g16_02 and g06_12, 2026-10-21).
    out["final_is_axiom"] = any(ax["name"] == "final" for ax in ast["axioms"])
    # Contents given as text (a hard flaw, the user 2026-10-21: "当然算硬伤了"): a constant or constructor that makes an
    # eventuality or a content out of a string, such as Content "Renee is warm with the boys". What the content says
    # is then hidden in an unanalysed sentence, so no step can use who does what to whom. A relation between a thing
    # and its wording (TextOf e s : bool) is not this: there the wording is recorded, not used as the content.
    def is_text(ty):
        return ty["kind"] == "type_application" and (ty["name"] == "string" or
               (ty["name"] == "list" and ty["arguments"] and ty["arguments"][0].get("name") == "char"))
    text_makers = set()
    for t in [x["conclusion"] for x in ast["axioms"] + ast["definitions"] + ast["theorems"] + ast["theorem_values"]]:
        for x in walk(t):
            if own(x):
                dom, rng = arrow(x["type"])
                if any(is_text(d) for d in dom) and rng.get("name") != "bool":
                    text_makers.add(x["name"])
    # HOL4's own datatype constants (T_CASE, T_size, record updates) are not the model's: a case constant whose
    # branches are strings maps things to wording, as TextOf does, and makes nothing out of text (GPT g23_05, v24)
    out["text_contents"] = sorted(n for n in text_makers if not (n.endswith(("_CASE", "_size", "_fupd")) or "." in n))
    out["defined_truth_functions"] = sorted(takes_bool & defined)
    # A conditional conclusion A ==> B whose antecedent the starting points already rule out is true only because
    # A is false (a paradox of material implication): it says nothing about what follows from A.
    out["vacuous"] = []
    allf = [start_f[i] for i in sorted(switch)]
    for j, goal in (goal_of.items() if out["consistent"] == "consistent" else []):
        c = conjuncts(con)[j - 1]
        a, b = split_imp(strip_forall(c)[1])
        if a is None or strip_forall(c)[0]:
            continue
        af = translate(a)[0]
        if af is not None and entails(allf, z3.Not(af)) == "yes":
            out["vacuous"].append(j)
    # Two named things the starting points force to be one: names that were meant to pick out different things
    # (two acts, two contents, two people) are identified by the axioms.
    out["identified"] = []
    named = {}
    for i in sorted(switch):
        for x in walk(starts[i][1]):
            if own(x) and usort(x["type"]) and not arrow(x["type"])[0]:
                named[x["name"]] = x["type"]
    names = sorted(named) if out["consistent"] == "consistent" else []
    for ai, a in enumerate(names):
        for b in names[ai + 1:]:
            if named[a] != named[b]:
                continue
            az, bz = const(a, named[a])[0], const(b, named[b])[0]
            if entails(allf, az == bz) == "yes":
                out["identified"].append([a, b])
    # Circularity: a starting point that already says a conclusion, using only the definitions and the biconditional
    # starting points (bridges such as Forbidden e <=> Wrong e or True p = Unlawful c), and no other principle or fact.
    # Every link between two names must be written in a checked argument, so a conclusion hidden in a premise under
    # another name passes through one of these and is found here.
    #   restated     the starting point gives the conclusion on its own, without definitions or bridges: the final
    #                repeats a premise ("the decision is yours"), which the user does not count as circular
    #   equivalent   only through definitions or bridges, the starting point says the same as the conclusion in
    #                other words: a warning, not a flaw (the user, 2026-10-20: "不太行。可以给个警告。")
    #   contained    as equivalent, but the conclusion is only part of what the starting point says (a warning)
    def is_bridge(t):
        h, args = strip_comb(strip_forall(t)[1])
        return h["kind"] == "constant" and h["name"] == "=" and len(args) == 2 and arrow(h["type"])[0][0].get("name") == "bool"
    bridge_ids = [i for i, (n, p) in enumerate(starts) if i in switch and is_bridge(p)]
    out["bridges"] = [starts[i][0] for i in bridge_ids]
    out["circular"] = []
    bare = z3.Solver(); bare.set("timeout", time_ms)    # no definitions, no bridges
    if out["consistent"] == "consistent":
        for j, goal in goal_of.items():
            bf = [start_f[b] for b in bridge_ids]
            r = entails(bf, goal)
            if r == "yes":
                out["circular"].append({"conclusion": j, "start": None, "kind": "from definitions and bridges alone"})
                continue
            for i in sorted(switch):
                bf = [start_f[b] for b in bridge_ids if b != i]
                if entails(bf + [start_f[i]], goal) != "yes":
                    continue
                bare.push(); bare.add(start_f[i], z3.Not(goal)); plain = bare.check(); bare.pop()
                if plain == z3.unsat:
                    out["circular"].append({"conclusion": j, "start": starts[i][0], "kind": "restated"})
                    continue
                back = entails(bf + [goal], start_f[i],
                               ([starts[b][1] for b in bridge_ids if b != i] + [goal_hol_of[j]], starts[i][1]))
                out["circular"].append({"conclusion": j, "start": starts[i][0],
                                        "kind": {"yes": "equivalent", "no": "contained", "unknown": "contained (equivalence unknown)"}[back]})
    used = {n for rec in out["conclusions"] for m in rec.get("supports", []) for n in m}
    all_complete = all(rec.get("complete", False) for rec in out["conclusions"] if rec.get("follows_from_all") == "follows")
    out["isolated"] = [n for i, (n, _) in enumerate(starts) if i in switch and n not in used]
    out["isolated_settled"] = all_complete
    # Generality (a measure, not a flaw): a principle that names particular things (a person, an act, a number) holds
    # only for this case, and cannot be tested on other cases or used to check the argument's other judgments (Hare's
    # universalizability). Principles are the starting points (axioms, or premises stated in final) with a quantifier or
    # an "if", and the definitions; facts without either name particular things by nature and are not counted. A
    # quantified fact ("no evidence for c11 is current") is counted too, and the list shows what it names.
    def particulars(t):
        found = set()
        for x in walk(t):
            if x["kind"] == "constant" and x["name"] == "NUMERAL":
                found.add("a number")
            elif own(x) and not arrow(x["type"])[0]:
                found.add(x["name"])
        return sorted(found)
    def is_principle(t):
        return any(x["kind"] == "constant" and x["name"] in ("!", "?", "==>") for x in walk(t))
    ax_gen = [[n, particulars(t)] for n, t in starts if n.startswith("axiom ") and is_principle(t)]
    ax_gen += [["definition " + n, particulars(t)] for n, t in defs]
    pr_gen = [[n, particulars(t)] for n, t in starts if n.startswith("premise ") and is_principle(t)]
    out["generality"] = {"axioms": {"principles": len(ax_gen), "naming": [g for g in ax_gen if g[1]]},
                         "premises": {"principles": len(pr_gen), "naming": [g for g in pr_gen if g[1]]}}
    # Two flaws the deontic-logic literature agrees on (Chisholm 1963; Carmo and Jones 2002; the LogiKEy methodology,
    # Benzmüller, Parent and van der Torre 2020), checked without names wherever the argument has a predicate for
    # "happens" (a truth predicate, found from its truth bridges):
    #   collapse    a predicate P on eventualities is forced to hold of exactly what happens: for all x, P x <=> T x.
    #               P then says nothing beyond "it happens", as with modal collapse (what is possible or necessary
    #               is just what is actual) or deontic collapse (what ought to be is just what is).
    #   explosion   whether an eventuality the conclusions speak about (and whose truth no bridge defines, so an act
    #               or event rather than a content) happens is settled, and every smallest support
    #               for that uses a principle (a starting point with a quantifier or "if"): the principles decide
    #               what happens, so if it went the other way, as when an obligation is violated, the starting
    #               points would contradict each other (the contrary-to-duty problem). Settled by facts alone is fine.
    out["collapse"], out["explosion"], out["settled_by_facts"], out["trivial"] = [], [], [], []
    if out["consistent"] == "consistent" and truth:
        allf = [start_f[i] for i in sorted(switch)]
        unary = {}
        for t in [p for _, p in starts] + [d for _, d in defs] + [conjuncts(con)[j - 1] for j in goal_of]:
            for x in walk(t):
                if own(x):
                    dom, rng = arrow(x["type"])
                    if len(dom) == 1 and usort(dom[0]) in truth and rng.get("name") == "bool" \
                            and x["name"] not in truth[usort(dom[0])] and x["name"] not in defined:
                        unary[x["name"]] = (x["type"], usort(dom[0]))
        for P, (pty, srt) in sorted(unary.items()):
            pz = const(P, pty)[0]
            v = z3.Const("v__collapse", sorts[srt])
            for T, tty in truth[srt].items():
                tz = const(T, tty)[0]
                if entails(allf, z3.ForAll([v], pz(v) == tz(v))) == "yes":
                    out["collapse"].append([P, T])
            if entails(allf, z3.ForAll([v], pz(v))) == "yes":
                out["trivial"].append([P, "everything"])
            elif entails(allf, z3.ForAll([v], z3.Not(pz(v)))) == "yes":
                out["trivial"].append([P, "nothing"])
        # a constant whose truth a bridge defines (T c = phi) is a content, a proposition; deriving that it holds is
        # ordinary reasoning, not a decision about what happens, so only constants without a bridge are tested
        bridged = set()
        for _, t in starts + defs:
            for x in walk(t):
                if x["kind"] != "application":
                    continue
                h, args = strip_comb(x)
                if h["kind"] == "constant" and h["name"] == "=" and len(args) == 2:
                    for side in args:
                        sh, sa = strip_comb(side)
                        if own(sh) and len(sa) == 1 and own(sa[0]) and usort(sa[0]["type"]) in truth \
                                and sh["name"] in truth[usort(sa[0]["type"])]:
                            bridged.add(sa[0]["name"])
        evaluated = {}
        for j in goal_of:
            for x in walk(conjuncts(con)[j - 1]):
                if own(x) and not arrow(x["type"])[0] and usort(x["type"]) in truth and x["name"] not in bridged:
                    evaluated[x["name"]] = x["type"]
        principle_ids = {i for i in switch if is_principle(starts[i][1])}
        for e, ety in sorted(evaluated.items()):
            ez = const(e, ety)[0]
            for T, tty in truth[usort(ety)].items():
                tz = const(T, tty)[0]
                for lit, word in ((tz(ez), "happens"), (z3.Not(tz(ez)), "does not happen")):
                    if entails(allf, lit) != "yes":
                        continue
                    g = z3.Bool(f"settle_{e}_{T}_{len(word)}")
                    lit_h = h_app(h_const(T, tty), h_const(e, ety))
                    solver.add(z3.Implies(g, z3.Not(lit))); goal_formula[g.get_id()] = lit
                    goal_hol[g.get_id()] = lit_h if word == "happens" else h_neg(lit_h)
                    supports, complete = marco(g)
                    rec = {"eventuality": e, "predicate": T, "settled": word,
                           "supports": [[starts[i][0] for i in m] for m in supports], "complete": complete}
                    if supports and all(set(m) & principle_ids for m in supports):
                        out["explosion"].append(rec)
                    else:
                        out["settled_by_facts"].append(rec)
    # Creative definitions (a hard flaw; the standard criteria for definitions, conservativeness and eliminability,
    # Belnap 1993 "On Rigorous Definitions"): a definition only abbreviates, so nothing new may follow from it. HOL4's
    # own definitions are conservative by construction, but a predicate given two definitions (a HOL definition and an
    # axiom, or two axioms, each P x1 .. xn <=> body with distinct bound x's and P not in body) is defined twice, and
    # the two together claim body1 <=> body2. If nothing else in the argument gives that, the definitions created it.
    def explicit_def(t):
        vs, body = strip_forall(t)
        h, args = strip_comb(body)
        if not (h["kind"] == "constant" and h["name"] == "=" and len(args) == 2
                and arrow(h["type"])[0] and arrow(h["type"])[0][0].get("name") == "bool"):
            return None
        lh, largs = strip_comb(args[0])
        names = [v["name"] for v in vs]
        if not own(lh) or len(largs) != len(vs) or any(a["kind"] != "variable" for a in largs) \
                or [a["name"] for a in largs] != names or len(set(names)) != len(names) \
                or mentions_ast(args[1], lh):
            return None
        return lh["name"], largs, args[1]
    def subst_vars(t, mp):
        if t["kind"] == "variable" and t["name"] in mp:
            return mp[t["name"]]
        if t["kind"] == "application":
            return {**t, "function": subst_vars(t["function"], mp), "argument": subst_vars(t["argument"], mp)}
        if t["kind"] == "abstraction":
            inner = {k: v for k, v in mp.items() if k != t["variable"]["name"]}
            return {**t, "body": subst_vars(t["body"], inner)}
        return t
    defs_of = {}
    for i, (n, t) in enumerate(starts):
        if i in switch and (d := explicit_def(t)):
            defs_of.setdefault(d[0], []).append((n, i, d))
    for n, t in defs:
        if (d := explicit_def(t)):
            defs_of.setdefault(d[0], []).append(("definition " + n, None, d))
    out["creative"], out["creative_candidates"] = [], []
    if out["consistent"] == "consistent":
        for P, ds in sorted(defs_of.items()):
            for (na, ia, (_, va, ba)), (nb, ib, (_, vb, bb)) in itertools.combinations(ds, 2):
                fresh = [{"kind": "constant", "theory": theory, "name": f"{P}__arg{k}", "type": v["type"]} for k, v in enumerate(va)]
                fa = translate(subst_vars(ba, {v["name"]: c for v, c in zip(va, fresh)}))[0]
                fb = translate(subst_vars(bb, {v["name"]: c for v, c in zip(vb, fresh)}))[0]
                if fa is None or fb is None:
                    continue
                rest = [start_f[i] for i in sorted(switch) if i not in (ia, ib)]
                rest_h = [starts[i][1] for i in sorted(switch) if i not in (ia, ib)]
                bodies_h = h_eq(subst_vars(ba, {v["name"]: c for v, c in zip(va, fresh)}),
                                subst_vars(bb, {v["name"]: c for v, c in zip(vb, fresh)}))
                r = entails(rest, fa == fb, (rest_h, bodies_h))
                if r == "no":
                    out["creative"].append([P, na, nb])
                elif r == "unknown":
                    out["creative_candidates"].append([P, na, nb])
    out["countermodels"] = countermodels
    out["countermodel_failures"] = failures
    out["limits_hit"] = [k for k, v in limits.items() if v]
    out["unknown_why"] = {k: v for k, v in unknown_why.items() if v}
    if out["untranslatable"]:
        out["unknown_why"]["statements left out"] = len(out["untranslatable"])
    return out


def report(out, run):
    L = [f"Z3 engine on {run.name}: three states (follows / does not, with a countermodel checked in HOL semantics / unknown)", ""]
    if out.get("limits_hit"):
        L.append("NOT SETTLED: stopped by " + " and ".join({"budget": "the time budget", "marco": "the cap on MARCO steps",
                                                            "supports": "the cap of 50 smallest supports per conclusion"}[k]
                                                           for k in out["limits_hit"]) + "; questions after that are unknown")
        L.append("")
    if out["untranslatable"]:
        L.append("Left out (could not be translated): " + "; ".join(f"{n} ({e})" for n, e in out["untranslatable"]))
        L.append("")
    if out.get("unknown_why"):
        L.append("Answers 'unknown', by reason: " + "; ".join(f"{k}: {v}" for k, v in out["unknown_why"].items()))
    if out.get("countermodels"):
        c = out["countermodels"]
        L.append(f"Countermodels checked in HOL semantics: {c.get('validated', 0)} held up, {c.get('not validated', 0)} did not "
                 "(those answers are unknown, never 'does not')")
        L.append("")
    if out.get("generic"):
        L.append("Translated by the generic encoding (functions as objects, lambdas lifted, library constants uninterpreted); "
                 "an answer 'does not follow' resting on these is reported as unknown: " + ", ".join(out["generic"]))
        L.append("")
    L.append("Consistency of all starting points: " + out["consistent"]
             + (" — smallest contradictory set: " + ", ".join(out["contradiction"]) if out.get("contradiction") else ""))
    if out.get("consistent") == "inconsistent":
        if out.get("contradiction_confirmed_by_hol4"):
            L.append("  CONFIRMED by HOL4: the source replays with a proof that these starting points imply falsity (hard flaw)")
        else:
            L.append("  NOT CONFIRMED by HOL4 (" + json.dumps({k: v for k, v in out.get("hol4_confirmation", {"not": "tried"}).items() if k != "results"}) + "): a candidate only, not counted as a hard flaw")
    L.append("")
    L.append("Every smallest set of starting points that gives each conclusion of final:")
    for rec in out["conclusions"]:
        if rec["untranslatable"]:
            L.append(f"  conclusion {rec['j']}: not translated ({rec['untranslatable']})"); continue
        L.append(f"  conclusion {rec['j']}: from all starting points: {rec['follows_from_all']}")
        for m in rec.get("supports", []):
            L.append("    {" + ", ".join(m) + "}")
        if "complete" in rec:
            L.append("    " + ("complete: every smallest set is listed" if rec["complete"] else "NOT settled: some questions came back unknown"))
    L.append("")
    L.append("Every place of every predicate, tested inside each smallest support (truth predicates: "
             + ("; ".join(f"{k}: {', '.join(v)}" for k, v in out["truth_predicates"].items()) or "none") + ")")
    if out.get("positions_supports_tested"):
        L.append("  tested in the first 5 smallest supports only: " + ", ".join(
            f"conclusion {j} ({a} of {n})" for j, (a, n) in sorted(out["positions_supports_tested"].items(), key=lambda x: int(x[0]))))
    if out["untested_sorts"]:
        L.append("  no truth predicate for " + ", ".join(out["untested_sorts"]) + ": its places are tested for 'anything can stand there' only")
    L.append("  takes a truth value itself (transparent by type): " + (", ".join(out["takes_truth_value"]) or "none"))
    order = {"transparent": 0, "unknown": 1, "opaque": 2, "gives the truth only": 3, "pinned": 4, "not needed": 5}
    words = {"anything there": "anything can stand there", "truth value only": "anything with the same truth value can stand there"}
    for pos in sorted(out["positions"], key=lambda x: (order[x["verdict"]], x["predicate"], x["argument"])):
        L.append(f"  {pos['verdict'].upper() if pos['verdict'] == 'transparent' else pos['verdict']:<22}{pos['predicate']}, argument {pos['argument']}")
        groups = {}
        for x in pos["results"]:
            if x["status"] in words or x["status"] == "unknown":
                groups.setdefault((x["filler"], x["status"]), []).append(f"{x['conclusion']}.{x['support']}")
        for (filler, st), where in groups.items():
            L.append(f"      in place of {filler}: {words.get(st, 'unknown')} (conclusion.support: {', '.join(where)})")
    L.append("")
    L.append("Contents given as text (hard flaw): a constant or constructor that makes a thing out of a string: "
             + (", ".join("HARD FLAW " + n for n in out.get("text_contents", [])) or "none"))
    L.append("Final asserted, not proved (hard flaw): " + ("HARD FLAW final is an axiom; HOL4 checked no step to it"
                                                          if out.get("final_is_axiom") else "no"))
    L.append("Misused logic (hard flaw): a declared constant with no definition that takes a truth value: "
             + (", ".join("HARD FLAW " + n for n in out.get("takes_truth_value", [])) or "none"))
    if not out.get("truth_predicates"):
        L.append("Collapse and explosion under violation (hard flaws): not testable; no predicate says whether something happens, so neither can arise")
    else:
        L.append("Collapse (hard flaw once HOL4 confirms it): a predicate forced to hold of exactly what happens: "
                 + (", ".join((f"HARD FLAW {x[0]} = {x[1]} (confirmed by HOL4)" if len(x) > 2 and x[2]
                               else f"candidate {x[0]} = {x[1]} (not confirmed by HOL4)") for x in out.get("collapse", [])) or "none"))
        L.append("Explosion under violation (hard flaw): the principles alone settle whether an evaluated eventuality happens: "
                 + ("none" if not out.get("explosion") else ""))
        for r in out.get("explosion", []):
            L.append(("  HARD FLAW (confirmed by HOL4)" if r.get("confirmed_by_hol4") else "  candidate (not confirmed by HOL4)")
                     + f": {r['eventuality']} {r['settled']} ({r['predicate']}); every smallest support uses a principle: "
                     + " | ".join("{" + ", ".join(m) + "}" for m in r["supports"]))
        if out.get("settled_by_facts"):
            L.append("  settled by facts, not counted: " + ", ".join(f"{r['eventuality']} {r['settled']}" for r in out["settled_by_facts"]))
        if out.get("trivial"):
            L.append("  predicates true of everything or nothing (listed, not counted): "
                     + ", ".join(f"{p} of {w}" for p, w in out["trivial"]))
    L.append("Creative definitions (hard flaw): a predicate defined twice, the two definitions claiming something nothing else gives: "
             + (", ".join(f"HARD FLAW {p} ({a}; {b})" for p, a, b in out.get("creative", [])) or "none"))
    if out.get("creative_candidates"):
        L.append("  candidates (no countermodel held up in HOL semantics, so not counted): "
                 + ", ".join(f"{p} ({a}; {b})" for p, a, b in out["creative_candidates"]))
    L.append("Conditional conclusions true only because the starting points rule out their 'if' part: "
             + (", ".join(f"conclusion {j}" for j in out.get("vacuous", [])) or "none"))
    L.append("Different names the starting points force to be the same thing: "
             + (", ".join(f"{a} = {b}" for a, b in out.get("identified", [])) or "none"))
    L.append("")
    g = out.get("generality", {})
    L.append("Generality (a measure, not a flaw): principles that name particular things")
    for key, label in (("axioms", "axioms with a quantifier or 'if', and definitions"),
                       ("premises", "premises of final with a quantifier or 'if' (often facts in general form)")):
        gg = g.get(key, {"principles": 0, "naming": []})
        L.append(f"  {label}: {len(gg['naming'])} of {gg['principles']}")
        for n, things in gg["naming"]:
            L.append(f"    {n}: {', '.join(things)}")
    L.append("")
    L.append("Restated premises: a starting point that already says a conclusion, using only definitions and the biconditional starting points ("
             + (", ".join(out.get("bridges", [])) or "none") + ")")
    if out["consistent"] != "consistent":
        L.append("  not checked: the starting points are not shown consistent")
    elif not [c for c in out.get("circular", []) if c["kind"] != "restated"]:
        L.append("  none")
    restated = [c for c in out.get("circular", []) if c["kind"] == "restated"]
    if restated:
        L.append("  not counted (the final repeats a premise as it stands): "
                 + "; ".join(f"conclusion {c['conclusion']} from {c['start']}" for c in restated))
    for c in out.get("circular", []):
        if c["kind"] == "restated":
            continue
        if c["start"] is None:
            L.append(f"  conclusion {c['conclusion']} follows from the definitions and bridges alone")
        elif c["kind"] == "equivalent":
            L.append(f"  WARNING: conclusion {c['conclusion']} is {c['start']} in other words (only definitions and bridges between them)")
        else:
            L.append(f"  WARNING: conclusion {c['conclusion']} is part of {c['start']} in other words (only definitions and bridges between them)" + (" (equivalence unknown)" if "unknown" in c["kind"] else ""))
    L.append("")
    L.append("In no smallest set of any conclusion (isolated): " + (", ".join(out["isolated"]) or "none")
             + ("" if out["isolated_settled"] else "   (not settled: some lists are incomplete)"))
    return "\n".join(L) + "\n"


def confirm_in_hol4(run, out, host):
    """A Z3 answer is a candidate until HOL4 proves it. The source is replayed with one attempt per claim that rests on
    Z3 finding something unsatisfiable: a contradiction (the negation of the smallest contradictory set), a collapse
    (!x. P x = T x) and an explosion (whether the act happens, under final's stated premises), each proved by metis from
    the theory's axioms and definitions within 30 seconds. Only what HOL4 proves is confirmed."""
    import tempfile
    from pathlib import Path as P
    run = P(run).resolve()
    sys.path.insert(0, str(HERE.parent.parent))
    from native_check import check
    ast = json.loads((run / "native_check/kernel_ast.json").read_text())
    source = (run / "native_check/source.sml").read_text()
    in_db = any(t["name"] == "final" for t in ast.get("theorems", []) + ast.get("axioms", []))
    final_expr = 'DB.fetch "-" "final"' if in_db else "final"
    claims = []                                         # (tag, SML expression for the goal)
    if out.get("consistent") == "inconsistent":
        prem = [int(n.split()[1]) for n in out["contradiction"] if n.startswith("premise ")]
        axioms = [n.split(" ", 1)[1] for n in out["contradiction"] if n.startswith("axiom ")]
        claims.append(("contradiction",
            "let val chosen = map (fn i => List.nth (stated, i - 1)) [" + ", ".join(map(str, prem)) + "] "
            "in if null chosen then boolSyntax.F else boolSyntax.mk_neg (boolSyntax.list_mk_conj chosen) end",
            [json.dumps(a) for a in axioms]))
    for k, (pn, tn) in enumerate(out.get("collapse", [])):
        claims.append((f"collapse{k}",
            f'let val p = cst {json.dumps(pn)}; val t = cst {json.dumps(tn)}; '
            'val x = Term.mk_var ("x", fst (Type.dom_rng (Term.type_of p))) '
            'in under_stated (boolSyntax.mk_forall (x, boolSyntax.mk_eq (Term.mk_comb (p, x), Term.mk_comb (t, x)))) end',
            None))
    for k, r in enumerate(out.get("explosion", [])):
        lit = f'Term.mk_comb (cst {json.dumps(r["predicate"])}, cst {json.dumps(r["eventuality"])})'
        if r["settled"] != "happens":
            lit = f"boolSyntax.mk_neg ({lit})"
        claims.append((f"explosion{k}", f"under_stated ({lit})", None))
    if not claims:
        return {}
    lines = ["", "(* added by z3_engine.py: HOL4 checks the claims Z3 made by finding something unsatisfiable *)",
             "val _ = metisTools.limit := {time = SOME 30.0, infs = NONE};",
             "local",
             "  val thy = current_theory ();",
             "  fun cst n = Term.prim_mk_const {Name = n, Thy = thy};",
             "  fun allconj t = if boolSyntax.is_conj t then let val (a, b) = boolSyntax.dest_conj t in allconj a @ allconj b end else [t];",
             f"  val fin_body = snd (boolSyntax.strip_forall (Thm.concl ({final_expr})));",
             "  val stated = if boolSyntax.is_imp fin_body then allconj (fst (boolSyntax.dest_imp fin_body)) else [];",
             "  fun under_stated g = if null stated then g else boolSyntax.mk_imp (boolSyntax.list_mk_conj stated, g);",
             "  val all_axs = map snd (DB.axioms \"-\");",
             "  val defs = map snd (DB.definitions \"-\");",
             "  fun attempt tag axs goal =",
             "    (Tactical.prove (goal, METIS_TAC (axs @ defs) ORELSE (rpt strip_tac >> fs (axs @ defs) >> METIS_TAC (axs @ defs)));",
             "     print (\"Z3CONFIRM \" ^ tag ^ \" ok\\n\"))",
             "    handle _ => print (\"Z3CONFIRM \" ^ tag ^ \" fail\\n\");",
             "in"]
    for tag, goal, axioms in claims:
        axs = "map (fn n => DB.fetch \"-\" n) [" + ", ".join(axioms) + "]" if axioms is not None else "all_axs"
        lines.append(f"  val _ = attempt \"{tag}\" ({axs}) ({goal});")
    lines.append("end;")
    tmp = P(tempfile.mkdtemp(prefix="confirm_", dir=str(run / "z3_engine")))
    (tmp / "source.sml").write_text(source + "\n".join(lines) + "\n")
    res = check(tmp / "source.sml", tmp / "native_check", "hol4", host, timeout=600)
    log = (tmp / "native_check/native.log").read_text() if (tmp / "native_check/native.log").exists() else ""
    got = dict(re.findall(r"Z3CONFIRM (\w+) (ok|fail)", log))
    return {"status": res.get("status"), "folder": str(tmp.relative_to(run)),
            "results": {tag: got.get(tag) == "ok" for tag, _, _ in claims}}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--local", action="store_true"); ap.add_argument("--host", default="mini")
    ap.add_argument("--time-ms", type=int, default=5000)
    ap.add_argument("--budget-s", type=int, default=900, help="total seconds; later questions are answered unknown")
    ap.add_argument("--no-confirm", action="store_true", help="skip replaying a Z3 contradiction in HOL4")
    ap.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    a = ap.parse_args()
    run = Path(a.run)
    if a.worker:                                        # on the host: read the files next to this script
        ast = json.loads(Path("kernel_ast.json").read_text()); source = Path("source.sml").read_text()
        print(json.dumps(run_engine(ast, source, a.time_ms, a.budget_s)))
        return
    nc = run / "native_check"
    out_dir = run / "z3_engine"; out_dir.mkdir(exist_ok=True)
    if a.local:
        out = run_engine(json.loads((nc / "kernel_ast.json").read_text()), (nc / "source.sml").read_text(), a.time_ms, a.budget_s)
    else:
        remote = os.environ.get("HOLVERIFY_Z3_REMOTE_DIR", "thick_training/z3_engine").rstrip("/") + "/" + uuid.uuid4().hex
        subprocess.run(["ssh", "-o", "BatchMode=yes", a.host, "mkdir -p " + shlex.quote(remote)], check=True)
        subprocess.run(["scp", "-q", str(HERE), str(HERE.parent / "hol_semantics.py"), str(nc / "kernel_ast.json"), str(nc / "source.sml"), f"{a.host}:{remote}/"], check=True)
        cmd = f"cd {shlex.quote(remote)} && {VENV_PY} z3_engine.py x --worker --time-ms {a.time_ms} --budget-s {a.budget_s}"
        res = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", a.host, cmd],
                             capture_output=True, text=True, timeout=a.budget_s + 600)
        if res.returncode:
            (out_dir / "error.txt").write_text(res.stdout + res.stderr)
            raise SystemExit("Z3 engine failed; see z3_engine/error.txt")
        out = json.loads(res.stdout.strip().splitlines()[-1])
    if not a.no_confirm and (out.get("consistent") == "inconsistent" or out.get("collapse") or out.get("explosion")):
        try:
            c = confirm_in_hol4(run, out, a.host)
        except Exception as e:                          # no confirmation is no confirmation
            c = {"error": str(e), "results": {}}
        out["hol4_confirmation"] = c
        res = c.get("results", {})
        out["contradiction_confirmed_by_hol4"] = bool(res.get("contradiction"))
        for k, x in enumerate(out.get("collapse", [])):
            x.append(bool(res.get(f"collapse{k}")))
        for k, x in enumerate(out.get("explosion", [])):
            x["confirmed_by_hol4"] = bool(res.get(f"explosion{k}"))
    (out_dir / "z3_engine.json").write_text(json.dumps(out, indent=1))
    text = report(out, run)
    (out_dir / "z3_engine.txt").write_text(text)
    print(text)


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(200000)                      # long conjunctions nest deeply in the exported term tree
    threading.stack_size(512 * 1024 * 1024)
    result = {}
    def run():
        try:
            main()
        except SystemExit as e:                         # keep the exit status a failure would give in the main thread
            result["code"] = e.code
        except BaseException:
            import traceback; traceback.print_exc(); result["code"] = 1
    t = threading.Thread(target=run)
    t.start(); t.join()
    code = result.get("code")
    if isinstance(code, str):
        print(code, file=sys.stderr); sys.exit(1)
    sys.exit(code or 0)
