"""Write the review feedback for a round-1 argument from the checkers' results. No model call, no hand-written content.

  python3 tools/reply_check/feedback.py runs/DATE/RUN       # writes RUN/feedback/review_feedback.txt

Run hidden_premises.py, isolated_parts.py and argument_checks.py on the run first. Every line below is generated from
their HOL4 results and printed in the source's own HOL4 names. The message states findings only; it does not say which
of them are faults.
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from gloss_claims import split_imp, strip_comb               # noqa: E402

INFIX = {"/\\": "/\\", "\\/": "\\/", "==>": "==>", "=": "=", "<": "<", "<=": "<=", ">": ">", ">=": ">=", "+": "+",
         "-": "-", "*": "*"}
CLOSING = "Revise the argument where you think it should change."


def hol(n):
    """the term in HOL4's own ASCII syntax, with parentheses around every compound part"""
    if n["kind"] in ("variable", "constant"):
        name = n["name"].split(".")[-1]
        return {"T": "T", "F": "F"}.get(name, name)
    if n["kind"] == "abstraction":
        return f'(\\{hol(n["variable"])}. {hol(n["body"])})'
    h, args = strip_comb(n)
    if h["kind"] == "constant":
        name = h["name"]
        short = name.split(".")[-1]
        if short == "NUMERAL" and len(args) == 1:
            def value(m):
                hh, aa = strip_comb(m)
                if hh["kind"] == "constant" and hh["name"] == "ZERO":
                    return 0
                return 2 * value(aa[0]) + (1 if hh["name"] == "BIT1" else 2)
            try:
                return str(value(args[0]))
            except Exception:
                pass
        if short in ("!", "?") and len(args) == 1 and args[0]["kind"] == "abstraction":
            return f'({short}{hol(args[0]["variable"])}. {hol(args[0]["body"])})'
        if short == "~" and len(args) == 1:
            return "~" + wrap(args[0])
        if short in INFIX and len(args) == 2:
            return f"{wrap(args[0])} {INFIX[short]} {wrap(args[1])}"
        if short == "CONS":
            items = []
            while h["kind"] == "constant" and h["name"] == "CONS" and len(args) == 2:
                items.append(hol(args[0])); h, args = strip_comb(args[1])
            return "[" + "; ".join(items) + "]"
        if name.startswith("recordtype.") and ".seldef." in name and len(args) == 1:
            return f"{wrap(args[0])}.{short}"
    return " ".join([wrap(h)] + [wrap(a) for a in args])


def wrap(n):
    text = hol(n)
    atomic = n["kind"] in ("variable", "constant") or (text.startswith("[") and text.endswith("]"))
    return text if atomic or (text.startswith("(") and text.endswith(")") and text.count("(") == 1) else f"({text})"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--final", default="final")
    a = ap.parse_args()
    run = Path(a.run)
    source = (run / "native_check/source.sml").read_text()
    ast = json.loads((run / "native_check/kernel_ast.json").read_text())
    every = {t["name"]: t for t in ast["theorem_values"] + ast["theorems"] + ast["definitions"]}
    ants, cons = split_imp(every[a.final]["conclusion"])
    P = {i + 1: hol(p) for i, p in enumerate(ants)}
    C = {j + 1: hol(c) for j, c in enumerate(cons)}
    load = lambda d: json.loads((run / d / f"{d}.json").read_text())["facts"]
    hp, ip, ac = load("hidden_premises"), load("isolated_parts"), load("argument_checks")
    get = lambda facts, k: [f for f in facts if f[0] == k]
    nums = lambda s: [int(x) for x in s.split(",") if x]

    L = [f"A checker ran HOL4 on your argument. These are its findings about theorem {a.final}, in your own names.", ""]
    ok = (get(ac, "consistent_final") or [["", ""]])[0][1] == "true"
    L.append(f"- The premises of {a.final} " + ("can all be true together." if ok else "cannot all be true together."))
    needed = [f[1] for f in get(hp, "needed") if f[2] == "true"]
    if needed:
        L.append(f"- {a.final} depends on these definitions besides its stated premises: " + ", ".join(needed) + ".")
    unused = [f[1] for f in get(ip, "definition") if f[2] == "true"]
    if unused:
        L.append(f"- {a.final} does not use these definitions: " + ", ".join(unused) + ".")
    declared = re.findall(r'new_constant\s*\(\s*"([^"]+)"', source)
    used = set()
    def collect(n):
        if n["kind"] in ("variable", "constant"):
            used.add(n["name"].split(".")[-1])
        elif n["kind"] == "application":
            collect(n["function"]); collect(n["argument"])
        elif n["kind"] == "abstraction":
            collect(n["body"])
    collect(every[a.final]["conclusion"])
    for d in needed:
        if d in every:
            collect(every[d]["conclusion"])
    undefined = [c for c in declared if c in used and any(c in hol(x) for x in ants + cons)]
    preds = sorted({f[1] for f in get(ac, "status")})
    primitive = [c for c in undefined if c in preds or c not in {hol(x) for x in ants}]
    if primitive:
        L.append(f"- These constants of {a.final} have no definition; its premises are all that constrain them: "
                 + ", ".join(primitive) + ".")
    outside = get(ip, "theorem")
    out_lines = []
    for f in outside:
        if f[3] == "false":
            _, tc = split_imp(every[f[1]]["conclusion"])
            out_lines.append(f"{hol(tc[int(f[2]) - 1])} ({f[1]})")
    if out_lines:
        L.append(f"- {a.final}'s premises do not give these conclusions of other theorems: " + "; ".join(out_lines) + ".")
    ctor_lines = []
    for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S):
        body = m.group(1) or m.group(2)
        for decl in body.split(";"):
            if "=" in decl and "<|" not in decl:
                for alt in decl.split("=", 1)[1].split("|"):
                    k = alt.strip().split()[0] if alt.strip() else ""
                    if k and k not in used:
                        in_any = any(k in hol(t["conclusion"]) for n, t in every.items() if n in [x["name"] for x in ast["theorem_values"]])
                        ctor_lines.append(k + ("" if in_any else " (in no theorem)"))
    if ctor_lines:
        L.append(f"- These constructors do not appear in {a.final}: " + ", ".join(ctor_lines) + ".")
    core = nums((get(ip, "core") or [["", ""]])[0][1])
    idle = [i for i in P if core and i not in core]
    if idle:
        L.append(f"- {a.final}'s conclusions still follow without these premises: " + "; ".join(P[i] for i in idle) + ".")
    support = {int(f[1]): nums(f[2]) for f in get(ip, "support")}
    parent = {j: j for j in C}
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for j in C:
        for k in C:
            if j < k and set(support.get(j, [])) & set(support.get(k, [])):
                parent[find(k)] = find(j)
    groups = {}
    for j in C:
        groups.setdefault(find(j), []).append(j)
    if len(groups) > 1:
        parts = ["{" + "; ".join(C[j] for j in js) + "}" for js in groups.values()]
        L.append(f"- {a.final}'s conclusions fall into {len(groups)} groups that share no premise: " + " ".join(parts) + ".")
    for f in get(ac, "support"):
        j, sup, then = int(f[1]), nums(f[2]), nums(f[3])
        if then:
            L.append(f"- {C[j]} is the consequent of the premise {P[then[0]]}.")
        elif len(sup) == 1:
            L.append(f"- {C[j]} follows from the single premise {P[sup[0]]}.")
    argued = {int(f[1]): f[2] for f in get(ac, "argued")}
    unargued = [P[i] for i in P if not argued.get(i) and (("==>" in P[i]) or any(p in P[i] for p in preds))]
    if unargued:
        L.append("- No theorem argues for these premises (premises stating the user's facts are not listed): " + "; ".join(unargued) + ".")
    how = {int(f[1]): f[2] for f in get(ac, "how")}
    for f in get(ac, "flip"):
        i, j, v = int(f[1]), int(f[2]), f[3]
        if v == "opposite":
            what = "With " + P[i] + (" left out" if how.get(i) == "left_out" else " false")
            neg = C[j][1:] if C[j].startswith("~") else "~" + (C[j] if C[j].startswith("(") else f"({C[j]})")
            L.append(f"- {what}, the other premises give {neg}.")
    stated = set(C.values()) | set(P.values())        # what final already says, as a conclusion or as a premise
    extra_true, extra_false, open_ = [], [], []
    for f in get(ac, "status"):
        t = f"{f[1]} {f[2]}"
        if f[3] == "true" and t not in stated:
            extra_true.append(t)
        elif f[3] == "false" and f"~{t}" not in stated and f"~({t})" not in stated and f"~{t.split()[0]} {t.split()[1]}" not in stated:
            extra_false.append(f"~{t}")
        elif f[3] == "open":
            open_.append(t)
    if extra_true or extra_false:
        L.append(f"- {a.final}'s premises also give, without {a.final} stating it: " + "; ".join(extra_true + extra_false) + ".")
    if open_:
        L.append(f"- {a.final}'s premises settle neither these nor their negations: " + "; ".join(open_) + ".")
    L += ["", CLOSING]
    out = run / "feedback"; out.mkdir(exist_ok=True)
    (out / "review_feedback.txt").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
