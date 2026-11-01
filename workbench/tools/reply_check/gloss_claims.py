"""Turn a checked HOL4 argument into English claims using the model's own notation comments. No model call.

  python3 tools/reply_check/gloss_claims.py runs/RUN            # writes runs/RUN/gloss_claims/claims.json and claims.txt

Glosses come only from the source's comments:
  - the "Notation:" comment, one "name args : gloss" entry per line (indented lines continue the gloss);
    the gloss's own parameter words are replaced by the rendered arguments
  - a comment right before "Definition name_def:" glosses that constant ("View 3: ..." keeps its label)
Unglossed names are shown with underscores as spaces. The terms come from kernel_ast.json (what HOL4 checked).
Claims: every distinct premise of every theorem, every conclusion conjunct, and each theorem as a whole.
"""
import argparse, json, re
from pathlib import Path

LOGIC = {"/\\", "\\/", "==>", "~", "=", "!", "?", "T", "F"}


def glosses(source):
    """notation entries ("name args : meaning" or "name args = meaning", in any comment) and view comments"""
    notation, views = {}, {}
    entry = re.compile(r"^\s*([A-Za-z_][\w']*)((?:\s+(?:[A-Za-z_][\w']*|\.\.\.))*)\s+[:=]\s+(.*)$")
    for m in re.finditer(r"\(\*(.*?)\*\)", source, re.S):
        body = m.group(1).strip()
        text = body[len("Notation:"):] if body.startswith("Notation:") else body
        found, last = {}, None
        for line in text.split("\n"):
            e = entry.match(line)
            if e:
                last = e.group(1)
                found[last] = {"params": e.group(2).split(), "gloss": e.group(3).strip()}
            elif last and line.strip() and line[:1].isspace():      # an indented line continues the entry above it
                found[last]["gloss"] += " " + line.strip()
            else:
                last = None
        if found:
            notation.update(found)
            continue
        d = re.match(r"\s*Definition\s+([A-Za-z_][\w']*?)(?:_def)?\s*:", source[m.end():])
        if d:
            label = re.match(r"^((?:[A-Za-z0-9]+ ?){1,4}):\s*(.*)$", body, re.S)    # a short label before a colon: "View 3: ..."
            views[d.group(1)] = {"label": label.group(1) if label else None,
                                 "gloss": " ".join((label.group(2) if label else body).split())}
    return notation, views


def strip_comb(n):
    args = []
    while n["kind"] == "application":
        args.insert(0, n["argument"]); n = n["function"]
    return n, args


def strip_forall(n):
    while True:
        h, args = strip_comb(n)
        if h["kind"] == "constant" and h["name"] == "!" and len(args) == 1 and args[0]["kind"] == "abstraction":
            n = args[0]["body"]
        else:
            return n


def conjuncts(n):
    h, args = strip_comb(n)
    if h["kind"] == "constant" and h["name"] == "/\\" and len(args) == 2:
        return conjuncts(args[0]) + conjuncts(args[1])
    return [n]


def split_imp(n):
    n = strip_forall(n)
    h, args = strip_comb(n)
    if h["kind"] == "constant" and h["name"] == "==>" and len(args) == 2:
        return conjuncts(args[0]), conjuncts(args[1])
    return [], conjuncts(n)


class Renderer:
    def __init__(self, notation, views, definitions):
        self.notation, self.views, self.defs = notation, views, definitions

    def word(self, name):
        name = name.split(".")[-1]
        g = self.notation.get(name)
        if g and not g["params"]:
            return g["gloss"]
        return name.replace("_", " ")

    def substitute(self, entry, args):
        params = [p for p in entry["params"] if p != "..."]
        if not params or len(params) != len(args):
            return entry["gloss"]
        text = dict(zip(params, (self.render(a) for a in args)))
        # a parameter spelled like an article ("a"): if it occurs once it is the parameter ("the reasons for a lose
        # their force"); if more than once, it is the article where a word follows it ("a stance against doing a")
        plain = r"\b(" + "|".join(map(re.escape, params)) + r")\b"
        clash = [q for q in params if q in ("a", "an") and len(re.findall(r"\b" + q + r"\b", entry["gloss"])) > 1]
        pattern = plain + r"(?!\s+[a-z])" if clash else plain
        return re.sub(pattern, lambda m: text[m.group(1)], entry["gloss"])

    def view(self, name):
        v = self.views[name]
        inside = [self.render(t) for t in self.glossed_parts(self.defs.get(name + "_def"))]
        text = f'the view that {v["gloss"]}'
        return text + (" (" + "; ".join(inside) + ")" if inside else "")

    def glossed_parts(self, d):
        """maximal applications inside a definition's right-hand side whose head the notation glosses"""
        if d is None:
            return []
        body = strip_forall(d["conclusion"])
        h, args = strip_comb(body)
        if h["kind"] == "constant" and h["name"] == "=" and len(args) == 2:
            body = args[1]
        found = []
        def walk(n):
            h, args = strip_comb(n)
            if h["kind"] == "constant" and h["name"].split(".")[-1] in self.notation and args:
                found.append(n); return
            for a in args:
                walk(a)
            if n["kind"] == "abstraction":
                walk(n["body"])
        walk(body)
        return found

    def render(self, n):
        if n["kind"] == "variable":
            return self.word(n["name"])
        if n["kind"] == "abstraction":
            return f'for any {self.word(n["variable"]["name"])}, {self.render(n["body"])}'
        h, args = strip_comb(n)
        if h["kind"] != "constant":
            return self.render(h) + " applied to " + ", ".join(self.render(a) for a in args)
        name = h["name"]
        if name == "NUMERAL" and len(args) == 1:          # HOL4 writes numbers in binary: BIT1 n = 2n+1, BIT2 n = 2n+2
            def value(n):
                hh, aa = strip_comb(n)
                if hh["kind"] == "constant" and hh["name"] == "ZERO":
                    return 0
                if hh["kind"] == "constant" and hh["name"] in ("BIT1", "BIT2") and len(aa) == 1:
                    return 2 * value(aa[0]) + (1 if hh["name"] == "BIT1" else 2)
                raise ValueError
            try:
                return str(value(args[0]))
            except ValueError:
                pass
        if name in ("CONS", "NIL"):
            items = []
            while h["kind"] == "constant" and h["name"] == "CONS" and len(args) == 2:
                items.append(self.render(args[0])); h, args = strip_comb(args[1])
            if not items:
                return "the empty list"
            return "the list of " + (", ".join(items[:-1]) + " and " + items[-1] if len(items) > 1 else items[0])
        if name == "~" and len(args) == 1:
            return "it is not the case that " + self.render(args[0])
        if name == "/\\" and len(args) == 2:
            return self.render(args[0]) + ", and " + self.render(args[1])
        if name == "\\/" and len(args) == 2:
            return "either " + self.render(args[0]) + ", or " + self.render(args[1])
        if name == "==>" and len(args) == 2:
            return "if " + self.render(args[0]) + ", then " + self.render(args[1])
        if name == "=" and len(args) == 2:
            return self.render(args[0]) + " is " + self.render(args[1])
        if name == "!" and len(args) == 1:
            return self.render(args[0])
        if name == "?" and len(args) == 1 and args[0]["kind"] == "abstraction":
            return f'there is some {self.word(args[0]["variable"]["name"])} such that {self.render(args[0]["body"])}'
        if name.startswith("recordtype.") and ".seldef." in name and len(args) == 1:
            field = name.split(".")[-1]
            g = self.notation.get(field)
            return f"{g['gloss']}, for {self.render(args[0])}" if g else f"the {field} of {self.render(args[0])}"
        short = name.split(".")[-1]
        if short in self.views:
            return self.view(short)
        if short in self.notation:
            return self.substitute(self.notation[short], args)
        if not args:
            return self.word(short)
        if len(args) == 2:
            return f"{self.render(args[0])} {self.word(short)} {self.render(args[1])}"
        return f"{self.word(short)} holds of " + " and ".join(self.render(a) for a in args)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run")
    a = ap.parse_args()
    run = Path(a.run); nc = run / "native_check" if (run / "native_check").is_dir() else run
    ast = json.loads((nc / "kernel_ast.json").read_text())
    notation, views = glosses((nc / "source.sml").read_text())
    defs = {d["name"]: d for d in ast["definitions"]}
    r = Renderer(notation, views, defs)
    claims, seen = [], set()
    def add(kind, theorem, text):
        if (kind, text) not in seen:
            seen.add((kind, text)); claims.append({"id": len(claims) + 1, "kind": kind, "theorem": theorem, "text": text})
    for t in ast["theorem_values"]:
        if t["name"] in defs or t["name"].endswith("_def"):
            continue
        ants, cons = split_imp(t["conclusion"])
        for p in ants:
            add("premise", t["name"], r.render(p))
        for c in cons:
            add("conclusion", t["name"], r.render(c))
        whole = " and ".join(r.render(p) for p in ants)
        body = "; ".join(r.render(c) for c in cons)
        if ants or len(cons) > 1:
            add("theorem", t["name"], f"If {whole}, then {body}" if ants else body)
    out = run / "gloss_claims"; out.mkdir(exist_ok=True)
    (out / "claims.json").write_text(json.dumps({"notation": notation, "views": views, "claims": claims}, indent=1, ensure_ascii=False))
    lines = [f'{c["id"]:>3} [{c["kind"]}, {c["theorem"]}] {c["text"]}' for c in claims]
    (out / "claims.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
