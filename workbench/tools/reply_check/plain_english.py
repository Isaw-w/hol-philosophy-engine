"""Read a checked HOL4 argument as stiff but ordinary English sentences. No model call.

  python3 tools/reply_check/plain_english.py runs/RUN              # writes runs/RUN/gloss_claims/plain.txt
  python3 tools/reply_check/plain_english.py runs/RUN --no-names   # plain_nonames.txt: each argument term written out in full
  python3 tools/reply_check/plain_english.py runs/RUN --bare       # plain_bare.txt: each argument term is the model's own comment, quoted
  python3 tools/reply_check/plain_english.py runs/RUN --annotate   # also plain_annotated.sml: the checked source with each
                                                                   # reading put in a comment beside its theorem or definition

Same glosses as gloss_claims.py (the model's own notation comments). Two standard sentence-planning steps keep every
sentence short: each glossed argument term gets a name once ("View 3 is the view that ...") and is referred to by that
name afterwards, and every conjunct becomes its own sentence. The sentence structure (not, and, if, which term goes
where) comes from the formula alone; the comments only supply words.
"""
import argparse, json
from pathlib import Path

from gloss_claims import Renderer, glosses, split_imp, strip_comb


STANDARD = {"bool", "min", "prim_rec", "arithmetic", "num", "list", "pair", "combin", "sat", "marker"}   # HOL4's own theories
ARITH = {"<": "is less than", "<=": "is at most", ">": "is greater than", ">=": "is at least"}


class Plain(Renderer):
    def __init__(self, *a, use_names=True, bare=False):
        super().__init__(*a)
        self.names, self.intro, self.use_names, self.bare, self.seen = {}, [], use_names and not bare, bare, set()
        self.intro_by_view = {}

    def view(self, name):
        v = self.views[name]
        if not self.use_names:
            text = f'"{v["gloss"]}"' if self.bare else f'the view that {v["gloss"]}'
            if name not in self.seen:      # what the definition says about it, as facts for the reader
                self.seen.add(name)
                lines = [sentence(f"{text} is {self.render(t)}") for t in self.glossed_parts(self.defs.get(name + "_def"))]
                self.intro += lines; self.intro_by_view[name] = lines
            return text
        if name not in self.names:
            v = self.views[name]
            label = v["label"] or f'the argument "{name.replace("_", " ")}"'
            self.names[name] = label
            lines = [f'{label} is the view that {v["gloss"]}.'] + [f"{label} is {self.render(t)}." for t in self.glossed_parts(self.defs.get(name + "_def"))]
            self.intro += lines; self.intro_by_view[name] = lines
        return self.names[name]

    def render(self, n):
        if n["kind"] == "variable":
            g = self.notation.get(n["name"])
            if g and not g["params"]:
                return g["gloss"]
            is_bool = n.get("type", {}).get("name") == "bool"      # a true-or-false switch, or a name for a thing
            return f'the condition "{self.word(n["name"])}" holds' if is_bool else self.word(n["name"])
        h, args = strip_comb(n)
        if h["kind"] == "constant":
            name = h["name"]
            if name == "~" and len(args) == 1:
                inner = strip_comb(args[0])[0]          # make the reach of "not" plain: not (A and B), not (A or B)
                both = inner["kind"] == "constant" and inner["name"] in ("/\\", "\\/")
                word = ("both " if inner["name"] == "/\\" else "either ") if both else ""
                return "it is not true that " + word + self.render(args[0])
            if name.startswith("recordtype.") and ".seldef." in name and len(args) == 1:
                field = name.split(".")[-1]
                g = self.notation.get(field)
                is_bool = h["type"]["arguments"][1].get("name") == "bool"     # a statement, or a noun inside one
                return f"for {self.render(args[0])}, {g['gloss']}" if g and is_bool else f"the {field} of {self.render(args[0])}"
            short = name.split(".")[-1]
            if name == "=" and len(args) == 2 and h["type"]["arguments"][0].get("name") == "bool":
                return f"{self.render(args[0])} exactly when {self.render(args[1])}"
            if short == "IN" and len(args) == 2:
                return f"{self.render(args[0])} is one of {self.render(args[1])}"
            if short == "LIST_TO_SET" and len(args) == 1:
                return self.render(args[0])
            if short in ("T", "F") and not args:
                return "true" if short == "T" else "false"
            if short in ARITH and len(args) == 2:
                return f"{self.render(args[0])} {ARITH[short]} {self.render(args[1])}"
            if h.get("theory") not in STANDARD and short not in self.views and short not in self.notation and len(args) == 2:
                return f'the relation "{self.word(short)}" holds between {self.render(args[0])} and {self.render(args[1])}'
        return super().render(n)


def sentence(text):
    return text[0].upper() + text[1:] + ("" if text.endswith(".") else ".")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run")
    ap.add_argument("--no-names", action="store_true")
    ap.add_argument("--bare", action="store_true")
    ap.add_argument("--annotate", action="store_true")
    a = ap.parse_args()
    run = Path(a.run); nc = run / "native_check" if (run / "native_check").is_dir() else run
    ast = json.loads((nc / "kernel_ast.json").read_text())
    notation, views = glosses((nc / "source.sml").read_text())
    defs = {d["name"]: d for d in ast["definitions"]}
    r = Plain(notation, views, defs, use_names=not a.no_names, bare=a.bare)
    body, records, per_theorem = [], [], {}
    for t in ast["theorem_values"]:
        if t["name"] in defs or t["name"].endswith("_def"):
            continue
        ants, cons = split_imp(t["conclusion"])
        body.append(f"Theorem {t['name']}:"); start = len(body)
        if ants:
            ps = [r.render(p) for p in ants]
            records += [{"theorem": t["name"], "kind": "premise", "text": sentence(p)} for p in ps]
            body.append("  " + sentence("if " + (", ".join(ps[:-1]) + ", and " + ps[-1] if len(ps) > 1 else ps[0]) + ", then the following hold"))
        cs = [sentence(r.render(c)) for c in cons]
        body += ["  " + c for c in cs]
        records += [{"theorem": t["name"], "kind": "conclusion", "text": c} for c in cs]
        per_theorem[t["name"]] = [l.strip() for l in body[start:]]
    out = run / "gloss_claims"; out.mkdir(exist_ok=True)
    head = "Names:" if r.use_names else "Facts from the definitions:"
    text = head + "\n" + "\n".join("  " + s for s in r.intro) + "\n\n" + "\n".join(body) + "\n"
    stem = "plain_bare" if a.bare else "plain_nonames" if a.no_names else "plain"
    (out / f"{stem}.txt").write_text(text)
    names = {}
    for line in (r.intro if r.use_names else []):
        label = next(v for v in r.names.values() if line.startswith(v + " "))
        names.setdefault(label, []).append(line)
    (out / f"{stem}.json").write_text(json.dumps({"names": names, "sentences": records}, indent=1, ensure_ascii=False))
    if a.annotate:
        annotated = annotate((nc / "source.sml").read_text(), per_theorem, r.intro_by_view)
        (out / f"{stem}_annotated.sml").write_text(annotated)
    print(text)


def comment(lines, indent=""):
    safe = [l.replace("(*", "( *").replace("*)", "* )") for l in lines]
    return [indent + "(* Plain reading, generated from the checked formula (HOL4 ignores comments):"] + \
           [indent + "     " + l for l in safe[:-1]] + [indent + "     " + safe[-1] + " *)"]


def annotate(source, per_theorem, per_view):
    """The source unchanged, with each plain reading in a comment: above its theorem, below its definition's End"""
    import re
    lines = source.split("\n"); out = []; pending_view = None
    for line in lines:
        m = re.match(r"^(Theorem|Triviality)\s+([A-Za-z_][\w']*)", line) or re.match(r"^val\s+([A-Za-z_][\w']*)\s*=", line)
        name = m.group(m.lastindex) if m else None
        if name in per_theorem and per_theorem[name]:
            out += comment(per_theorem[name])
        out.append(line)
        d = re.match(r"^Definition\s+([A-Za-z_][\w']*?)(?:_def)?\s*:", line)
        if d and d.group(1) in per_view:
            pending_view = d.group(1)
        elif pending_view and line.strip() == "End":
            if per_view[pending_view]:
                out += comment(per_view[pending_view])
            pending_view = None
    return "\n".join(out)


if __name__ == "__main__":
    main()
