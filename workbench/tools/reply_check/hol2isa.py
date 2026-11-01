"""Translate a checked HOL4 argument (native_check/kernel_ast.json, with the datatype declarations read from
source.sml) into an Isabelle/HOL theory for Nitpick.

The premises are those the Z3 engine uses: the conjuncts of final's antecedent (final's outer variables fixed as
constants), the axioms, and the argument's own definitions (HOL4's datatype internals left out). Own types become
typedecls or datatypes, own constants become fixed variables of the lemma, library constants map to their
Isabelle/HOL counterparts (a set 'a -> bool stays a predicate). Anything without a mapping raises Untranslatable.

  python3 hol2isa.py RUN > Arg.thy
"""
import json, re, sys
from pathlib import Path

sys.setrecursionlimit(100000)


class Untranslatable(Exception):
    pass


def ident(name, prefix):
    s = re.sub(r"[^A-Za-z0-9_']", "_", name)
    return prefix + s


def strip_comb(t):
    args = []
    while t["kind"] == "application":
        args.append(t["argument"]); t = t["function"]
    return t, args[::-1]


def strip_forall(t):
    vs = []
    while True:
        h, args = strip_comb(t)
        if h["kind"] == "constant" and h["name"] == "!" and len(args) == 1 and args[0]["kind"] == "abstraction":
            vs.append(args[0]["variable"]); t = args[0]["body"]
        else:
            return vs, t


def conjuncts(t):
    h, args = strip_comb(t)
    if h["kind"] == "constant" and h["name"] == "/\\" and len(args) == 2:
        return conjuncts(args[0]) + conjuncts(args[1])
    return [t]


def split_imp(t):
    h, args = strip_comb(t)
    if h["kind"] == "constant" and h["name"] == "==>" and len(args) == 2:
        return args[0], args[1]
    return None, t


def datatypes(source):
    """[(type name, [(constructor, [argument type text])])] in declaration order; records are not handled"""
    found = []
    bodies = [m.group(1) or m.group(2) for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S)]
    for body in bodies:
        for decl in re.split(r";|\n(?=\s*\w+\s*=)", body):
            if "=" not in decl:
                continue
            if "<|" in decl:
                raise Untranslatable("record type")
            name, rhs = decl.split("=", 1)
            alts = []
            for alt in [a.strip() for a in rhs.split("|") if a.strip()]:
                m = re.fullmatch(r"([A-Za-z_][\w']*)((?:\s+(?:[A-Za-z_][\w']*|\([^()]*\)))*)", alt, re.S)
                if not m:
                    raise Untranslatable("datatype syntax: " + alt[:60])
                args = re.findall(r"[A-Za-z_][\w']*|\([^()]*\)", m.group(2))
                alts.append((m.group(1), [a.strip("()").strip() for a in args]))
            found.append((name.strip(), alts))
    return found


class Printer:
    def __init__(self, ast, source):
        self.own = ast["theory"]
        self.dts = datatypes(source)
        self.dt_names = {n for n, _ in self.dts}
        self.ctors = {c for _, alts in self.dts for c, _ in alts}
        self.fixed = {}          # own constant name -> type
        self.own_types = {}      # own type name -> arity
        self.max_nat = 0         # the largest numeral, so that Nitpick's scope for nat holds it
        self.real = False

    # ---- types
    def ty(self, T):
        if T["kind"] != "type_application":
            return "'" + T["name"].lstrip("'")
        th, n, a = T["theory"], T["name"], T["arguments"]
        if th == "min" and n == "fun":
            return "(" + self.ty(a[0]) + " \\<Rightarrow> " + self.ty(a[1]) + ")"
        if th == "min" and n == "bool":
            return "bool"
        if th == "num" and n == "num":
            return "nat"
        if th == "realax" and n == "real":
            self.real = True
            return "real"
        if th == "string" and n == "char":
            return "char"
        if th == "list" and n == "list":
            return "(" + self.ty(a[0]) + " list)"
        if th == "option" and n == "option":
            return "(" + self.ty(a[0]) + " option)"
        if th == "pair" and n == "prod":
            return "(" + self.ty(a[0]) + " \\<times> " + self.ty(a[1]) + ")"
        if th == self.own:
            self.own_types[n] = len(a)
            name = ident(n, "ty_")
            return "(" + " ".join(self.ty(x) for x in a) + " " + name + ")" if a else name
        raise Untranslatable("type " + th + "$" + n)

    def src_ty(self, text):
        """a type as written in a Datatype declaration"""
        words = text.split()
        base = {"num": "nat", "bool": "bool", "string": "string", "char": "char", "real": "real"}
        out = []
        for w in words:
            if w in base:
                out.append(base[w])
            elif w in ("list", "option"):
                out.append(w)
            elif re.fullmatch(r"[A-Za-z_][\w']*", w):
                out.append(ident(w, "ty_"))
            else:
                raise Untranslatable("datatype argument type " + text)
        return '"' + " ".join(out) + '"'

    # ---- terms
    def num(self, t):
        h, args = strip_comb(t)
        if h["kind"] != "constant":
            return None
        n = h["name"]
        if h["theory"] == "num" and n == "0":
            return 0
        if h["theory"] == "arithmetic" and n == "ZERO":
            return 0
        if h["theory"] == "arithmetic" and n in ("BIT1", "BIT2") and len(args) == 1:
            v = self.num(args[0])
            return None if v is None else 2 * v + (1 if n == "BIT1" else 2)
        if h["theory"] == "arithmetic" and n == "NUMERAL" and len(args) == 1:
            return self.num(args[0])
        return None

    def string_lit(self, t):
        chars = []
        while True:
            h, args = strip_comb(t)
            if h["kind"] == "constant" and h["theory"] == "list" and h["name"] == "NIL":
                break
            if not (h["kind"] == "constant" and h["theory"] == "list" and h["name"] == "CONS" and len(args) == 2):
                return None
            ch, chargs = strip_comb(args[0])
            if not (ch["kind"] == "constant" and ch["theory"] == "string" and ch["name"] == "CHR" and len(chargs) == 1):
                return None
            v = self.num(chargs[0])
            if v is None:
                return None
            chars.append(v); t = args[1]
        if not chars:
            return None
        if all(32 <= c < 127 and chr(c) not in "'\\" for c in chars):
            return "''" + "".join(map(chr, chars)) + "''"
        return "[" + ", ".join("(char_of (%d::nat))" % c for c in chars) + "]"

    def binder(self, q, arg):
        if arg["kind"] == "abstraction":
            v = arg["variable"]
            return "(" + q + ident(v["name"], "v_") + "::" + self.ty(v["type"]) + ". " + self.tm(arg["body"]) + ")"
        return None

    def tm(self, t):
        k = t["kind"]
        if k == "variable":
            return ident(t["name"], "v_")
        if k == "abstraction":
            v = t["variable"]
            return "(\\<lambda>" + ident(v["name"], "v_") + "::" + self.ty(v["type"]) + ". " + self.tm(t["body"]) + ")"
        n = self.num(t)
        if n is not None:
            self.max_nat = max(self.max_nat, n)
            return "(%d::nat)" % n
        s = self.string_lit(t)
        if s is not None:
            return "(" + s + "::string)"
        h, args = strip_comb(t)
        if h["kind"] != "constant":
            return "(" + " ".join([self.tm(h)] + [self.tm(a) for a in args]) + ")"
        th, nm = h["theory"], h["name"]
        key = (th, nm)
        if key in (("bool", "!"), ("bool", "?"), ("bool", "?!"), ("min", "@")) and len(args) == 1:
            q = {"!": "\\<forall>", "?": "\\<exists>", "?!": "\\<exists>!", "@": "SOME "}[nm]
            b = self.binder(q, args[0])
            if b is not None:
                return b
            return "(" + {"!": "All", "?": "Ex", "?!": "Ex1", "@": "Eps"}[nm] + " " + self.tm(args[0]) + ")"
        A = [self.tm(a) for a in args]
        infix = {("bool", "/\\"): "\\<and>", ("bool", "\\/"): "\\<or>", ("min", "==>"): "\\<longrightarrow>",
                 ("min", "="): "=", ("arithmetic", "+"): "+", ("arithmetic", "-"): "-", ("arithmetic", "*"): "*",
                 ("prim_rec", "<"): "<", ("arithmetic", "<="): "\\<le>", ("arithmetic", ">"): ">",
                 ("arithmetic", ">="): "\\<ge>", ("arithmetic", "DIV"): "div", ("arithmetic", "MOD"): "mod",
                 ("arithmetic", "EXP"): "^", ("realax", "real_add"): "+", ("realax", "real_sub"): "-",
                 ("realax", "real_mul"): "*", ("realax", "/"): "/", ("real", "/"): "/", ("realax", "real_lt"): "<",
                 ("real", "real_lte"): "\\<le>", ("real", "real_gt"): ">", ("real", "real_ge"): "\\<ge>",
                 ("list", "CONS"): "#", ("list", "APPEND"): "@", ("pair", ","): ","}
        if key in infix:
            op = infix[key]
            if len(args) == 2:
                if op == ",":
                    return "(" + A[0] + ", " + A[1] + ")"
                return "(" + A[0] + " " + op + " " + A[1] + ")"
            fn = {"#": "Cons", "@": "append", ",": "Pair", "div": "(div)", "mod": "(mod)"}.get(op, "(" + op + ")")
            return "(" + " ".join([fn] + A) + ")" if A else fn
        simple = {("bool", "~"): "Not", ("bool", "T"): "True", ("bool", "F"): "False", ("num", "SUC"): "Suc",
                  ("list", "LENGTH"): "length", ("list", "MAP"): "map", ("list", "FILTER"): "filter",
                  ("list", "EVERY"): "list_all", ("list", "EXISTS"): "list_ex", ("list", "HD"): "hd",
                  ("list", "TL"): "tl", ("list", "REVERSE"): "rev", ("list", "SUM"): "sum_list",
                  ("pair", "FST"): "fst", ("pair", "SND"): "snd", ("pair", "UNCURRY"): "case_prod",
                  ("arithmetic", "MIN"): "min", ("arithmetic", "MAX"): "max", ("realax", "real_neg"): "uminus",
                  ("realax", "real_of_num"): "(of_nat :: nat \\<Rightarrow> real)", ("option", "SOME"): "Some"}
        if key in simple:
            return "(" + " ".join([simple[key]] + A) + ")" if A else simple[key]
        typed = {("list", "NIL"): "[]", ("bool", "ARB"): "undefined", ("option", "NONE"): "None"}
        if key in typed:
            base = "(" + typed[key] + "::" + self.ty(h["type"]) + ")"
            return "(" + " ".join([base] + A) + ")" if A else base
        if key == ("realax", "real_of_num") and len(args) == 1 and self.num(args[0]) is not None:
            return "(%d::real)" % self.num(args[0])
        if key == ("bool", "COND") and len(args) == 3:
            return "(if " + A[0] + " then " + A[1] + " else " + A[2] + ")"
        if key == ("bool", "LET") and len(args) == 2:
            return "(Let " + A[1] + " " + A[0] + ")"
        if key == ("bool", "IN") and len(args) == 2:          # a HOL4 set is a predicate
            return "(" + A[1] + " " + A[0] + ")"
        if key == ("list", "LIST_TO_SET") and len(args) == 1:
            return "(\\<lambda>x. x \\<in> set " + A[0] + ")"
        if key == ("list", "MEM") and len(args) == 2:
            return "(" + A[0] + " \\<in> set " + A[1] + ")"
        if key == ("list", "EL") and len(args) == 2:
            return "(" + A[1] + " ! " + A[0] + ")"
        if key == ("list", "FOLDR") and len(args) == 3:
            return "(foldr " + A[0] + " " + A[2] + " " + A[1] + ")"
        if key == ("string", "CHR") and len(args) == 1:
            return "(char_of " + A[0] + ")"
        if th == self.own:
            if nm.endswith("_CASE") and nm[:-5] in self.dt_names and args:
                return "(" + " ".join(["case_" + ident(nm[:-5], "ty_")] + A[1:] + [A[0]]) + ")"
            if re.search(r"_size$", nm) and nm[:-5] in self.dt_names:
                raise Untranslatable("size constant " + nm)
            if nm in self.ctors:
                c = ident(nm, "c_")
                return "(" + " ".join([c] + A) + ")" if A else c
            T = self.ty(h["type"])
            if self.fixed.get(nm, T) != T:
                raise Untranslatable("own constant at two types: " + nm)
            self.fixed[nm] = T
            c = ident(nm, "k_")
            return "(" + " ".join([c] + A) + ")" if A else c
        raise Untranslatable("constant " + th + "$" + nm)


def premises(ast, dt_names):
    """[(label, term)] as the Z3 engine numbers them, the definitions as background, and final's conclusion"""
    every = {t["name"]: t for t in ast["theorem_values"] + ast["theorems"] + ast["definitions"]}
    final = every["final"]["conclusion"]
    fvars, body = strip_forall(final)
    names = {v["name"] for v in fvars}
    def fix(t, names):
        if t["kind"] == "variable" and t["name"] in names:
            return {"kind": "constant", "theory": ast["theory"], "name": t["name"], "type": t["type"]}
        if t["kind"] == "application":
            return {**t, "function": fix(t["function"], names), "argument": fix(t["argument"], names)}
        if t["kind"] == "abstraction":
            return {**t, "body": fix(t["body"], names - {t["variable"]["name"]})}
        return t
    body = fix(body, names) if names else body
    ant, con = split_imp(body)
    stated = conjuncts(ant) if ant is not None else []
    starts = [("premise " + str(i + 1), p) for i, p in enumerate(stated)] + \
             [("axiom " + a["name"], a["conclusion"]) for a in ast["axioms"]]
    defs = [(d["name"], d["conclusion"]) for d in ast["definitions"]
            if not any(d["name"].startswith(ty + "_") for ty in dt_names)
            and not re.search(r"_(TY_DEF|case_def|size_def|repfns|bijections)$", d["name"])]
    return starts, defs, con


def theory(run, name="Arg", conclusion_timeout=60):
    run = Path(run)
    ast = json.loads((run / "native_check/kernel_ast.json").read_text())
    source = (run / "native_check/source.sml").read_text()
    P = Printer(ast, source)
    starts, defs, con = premises(ast, P.dt_names)
    defs_txt = [(n, P.tm(t)) for n, t in defs]
    starts_txt = [(n, P.tm(t)) for n, t in starts]
    lines = ["theory " + name + " imports " + ("Complex_Main" if P.real or "real" in source else "Main") + " begin", ""]
    for n, ar in sorted(P.own_types.items()):
        if n not in P.dt_names:
            tv = " ".join("'t%d" % i for i in range(ar))
            lines.append("typedecl " + ("(" + ", ".join("'t%d" % i for i in range(ar)) + ") " if ar > 1 else (tv + " " if ar else "")) + ident(n, "ty_"))
    for n, alts in P.dts:
        lines.append("datatype " + ident(n, "ty_") + " = " +
                     " | ".join(" ".join([ident(c, "c_")] + [P.src_ty(a) for a in args]) for c, args in alts))
    lines.append("")
    fixes = " and ".join(ident(n, "k_") + ' :: "' + T + '"' for n, T in sorted(P.fixed.items()))
    labels = []
    assumes = []
    for i, (n, s) in enumerate(defs_txt + starts_txt):
        labels.append(n)
        assumes.append("a%d: \"%s\"" % (i, s.replace('"', '\\"')))
    goals = [P.tm(c) for c in conjuncts(con)]          # final's conclusions, numbered as the Z3 engine numbers them
    opts = ", max_threads = 1" + (", card nat = %d" % (P.max_nat + 2) if P.max_nat >= 9 else "")
    # consistency: a model of all the assumptions falsifies False; conclusion j: a countermodel shows it does not follow
    for lemma, shows, timeout in [("consistency", "False", 300)] + \
                                 [("conclusion_%d" % j, g, conclusion_timeout) for j, g in enumerate(goals, 1)]:
        lines.append("lemma " + lemma + ":")
        if fixes:
            lines.append("  fixes " + fixes)
        if assumes:
            lines.append("  assumes " + "\n      and ".join(assumes))
        lines += ['  shows "' + shows.replace('"', '\\"') + '"', "  nitpick [timeout = %d%s]" % (timeout, opts), "  oops", ""]
    lines += ["end", ""]
    return "\n".join(lines), labels


if __name__ == "__main__":
    try:
        text, labels = theory(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "Arg")
    except Untranslatable as e:
        print("UNTRANSLATABLE:", e, file=sys.stderr); sys.exit(2)
    print(text)
