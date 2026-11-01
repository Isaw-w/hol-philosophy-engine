"""Write the round-2 message for a checked round-1 argument: its hidden premises and its isolated parts, then the question.
No model call. Every line is generated from the HOL4 results of hidden_premises.py and isolated_parts.py, in the source's
own HOL4 names.

  python3 tools/reply_check/review_message.py runs/DATE/RUN      # writes RUN/round2_message/message.txt
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from feedback import hol                                     # noqa: E402
from gloss_claims import split_imp                           # noqa: E402

QUESTION = ("If you think these are your intentions, leave the argument unchanged and convert your argument into a proper "
            "natural-language response to the original user query, citing the axioms and theorems after each sentence, "
            "with their names in square brackets, or [none] if a sentence does not come from the argument. "
            "If not, revise the argument and return it in a single HOL4 code block.")


def names_in(node, acc):
    if node["kind"] in ("variable", "constant"):
        acc.add(node["name"].split(".")[-1])
    elif node["kind"] == "application":
        names_in(node["function"], acc); names_in(node["argument"], acc)
    elif node["kind"] == "abstraction":
        names_in(node["variable"], acc); names_in(node["body"], acc)
    return acc


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--final", default="final")
    a = ap.parse_args()
    run = Path(a.run)
    source = (run / "native_check/source.sml").read_text()
    hp = json.loads((run / "hidden_premises/hidden_premises.json").read_text())["facts"]
    ip = json.loads((run / "isolated_parts/isolated_parts.json").read_text())["facts"]
    hk = json.loads((run / "hidden_premises/hol4/kernel_ast.json").read_text())
    ik = json.loads((run / "isolated_parts/hol4/kernel_ast.json").read_text())
    every = {t["name"]: t for t in hk["theorems"] + hk["theorem_values"] + hk["definitions"]}
    final = every[a.final]
    stated, cons = split_imp(final["conclusion"])
    alone_ok = {f[1].removeprefix("axiom ") for f in hp if f[0] == "needed" and f[2] == "false"}
    pieces = [(f[1], f[2]) for f in hp if f[0] == "piece"]
    all_items = [f[1] for f in hp if f[0] == "needed"]

    def label(src):
        m = re.match(r"^(axiom )?(.+?)(#\d+)?(\.(only_if|if|\w+))?$", src)
        name = src.removeprefix("axiom ")
        base = re.sub(r"#\d+.*$", "", name)
        part = ""
        if ".only_if" in name:
            part = ", left to right"
        elif ".if" in name:
            part = ", right to left"
        elif "#" in name and "." in name.split("#", 1)[1]:
            part = ", field " + name.rsplit(".", 1)[1]
        return base + part, base

    L = ["These are the hidden premises and the isolated parts of your argument, checked with HOL4.", ""]
    L.append("1. Hidden premises of final")
    if stated:
        L.append(f"final states {len(stated)} premise{'s' if len(stated) != 1 else ''}. A smallest set that, together with them, "
                 "gives final (each item is needed; leave any one out and final no longer follows):")
    else:
        L.append("final states no premises. A smallest set that gives final (each item is needed; leave any one out and final "
                 "no longer follows):")
    used = set()
    for n, (piece, src) in enumerate(pieces, 1):
        t = every.get(piece)
        if t is None:
            continue
        names_in(t["conclusion"], used)
        lab, base = label(src)
        star = " *" if base in alone_ok else ""
        L.append(f"  ({n}) {hol(t['conclusion'])}   [{lab}]{star}")
    if any(label(src)[1] in alone_ok for _, src in pieces):
        L.append("  * final still follows when this item alone is left out; it is needed only once the items in 2 are gone too.")
    declared = re.findall(r'new_constant\s*\(\s*"([^"]+)"', source)
    names_in(final["conclusion"], used)
    undefined = [c for c in declared if c in used]
    if undefined:
        L.append("These constants have no definition; final relies on what the items above say about them: " + ", ".join(undefined) + ".")
    L.append("")
    L.append("2. Isolated parts")
    in_set = {label(src)[1] for _, src in pieces}
    unused = [x.removeprefix("axiom ") for x in all_items if x.removeprefix("axiom ") not in in_set]
    if unused:
        L.append("These definitions and axioms are not in the set above: " + ", ".join(unused) + ".")
    unused_consts = [c for c in declared if c not in used]
    if unused_consts:
        L.append("These constants appear nowhere in final or in the set above: " + ", ".join(unused_consts) + ".")
    starts = {int(f[1]): f[2] for f in ip if f[0] == "start"}
    support = {int(f[1]): [int(x) for x in f[2].split(",") if x] for f in ip if f[0] == "support"}
    C = {j + 1: hol(c) for j, c in enumerate(cons)}
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
        L.append(f"final's conclusions fall into {len(groups)} groups whose supporting items do not overlap:")
        for js in groups.values():
            sup = sorted({starts[i].removeprefix("axiom ").removeprefix("premise") or f"premise {i}" for j in js for i in support.get(j, [])})
            L.append("  " + "; ".join(C[j] for j in js) + "   [from " + (", ".join(sup) if sup else "definitions alone") + "]")
    L += ["", QUESTION]
    out = run / "round2_message"; out.mkdir(exist_ok=True)
    (out / "message.txt").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
