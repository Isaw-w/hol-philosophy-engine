"""Check the citations in a review-round reply against the round-1 argument's checked hidden premises and isolated parts.
No model call, no new HOL4 run: it reads the earlier results.

  python3 tools/reply_check/reply_citations.py runs/DATE/REVIEW_RUN runs/DATE/ROUND1_RUN
      # writes REVIEW_RUN/citations/citations.txt, citations.json and reply_clean.txt (the reply without the citations)

A citation is a bracket, square or round, holding names of the round-1 source's axioms, theorems or definitions.
For every sentence it lists what the sentence cites, and whether each cited item is in the smallest set final rests on,
is isolated (final does not use it), or is another theorem. It also lists items of the smallest set no sentence cites,
sentences that cite nothing, and cited names the source does not have.
"""
import argparse, json, re
from pathlib import Path

BRACKET = re.compile(r"\s*[\[(]([^\[\]()]*)[\])]")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("review"); ap.add_argument("round1")
    a = ap.parse_args()
    rv, r1 = Path(a.review), Path(a.round1)
    reply_file = rv / "reply.txt" if (rv / "reply.txt").exists() else rv / "revised_response.txt"   # round 2 or round 3
    reply = reply_file.read_text().strip()
    source = (r1 / "native_check/source.sml").read_text()
    ast = json.loads((r1 / "native_check/kernel_ast.json").read_text())
    names = {t["name"] for t in ast["theorem_values"] + ast["theorems"] + ast.get("axioms", []) + ast["definitions"]}
    names |= set(re.findall(r"^Definition\s+([A-Za-z_][\w']*)", source, re.M))
    names |= {n.removesuffix("_def") for n in list(names) if n.endswith("_def")}
    definitions = {d["name"] for d in ast["definitions"]} | {d["name"].removesuffix("_def") for d in ast["definitions"]}
    if (r1 / "hidden_premises/hidden_premises.json").exists():
        hp = json.loads((r1 / "hidden_premises/hidden_premises.json").read_text())["facts"]
        core = {re.sub(r"#\d+.*$", "", f[2].removeprefix("axiom ")) for f in hp if f[0] == "piece"}
        every_item = {f[1].removeprefix("axiom ") for f in hp if f[0] == "needed"}
        alternatives = {re.sub(r"#\d+.*$", "", f[1].removeprefix("axiom ")) for f in hp if f[0] == "alternative"}
        isolated = every_item - core - alternatives
    else:                                               # the Z3 engine's lists: every axiom in some smallest support of a
        z = json.loads((r1 / "z3_engine/z3_engine.json").read_text())        # conclusion of final, and the isolated ones
        used = {n for c in z["conclusions"] for m in c.get("supports", []) for n in m}
        core = {n.removeprefix("axiom ") for n in used if n.startswith("axiom ")}
        isolated = {n.removeprefix("axiom ") for n in z["isolated"] if n.startswith("axiom ")}
        alternatives = set()
        every_item = core | isolated
    theorems = {t["name"] for t in ast["theorem_values"]} - {t["name"] for t in ast.get("axioms", [])} - every_item

    def kind(n):
        if n == "none":
            return "the model says this sentence does not come from the argument"
        n2 = n if n in core | isolated else (n + "_def" if n + "_def" in core | isolated else n)
        if n2 in core:
            return "in the set final rests on"
        if n2 in alternatives:
            return "can stand in for items of that set"
        if n2 in isolated:
            return "isolated (final does not use it)"
        if n in theorems:
            return "a theorem"
        if n in definitions:
            return "a definition"
        return "unknown"

    sentences = []
    for para in reply.split("\n"):
        for s in re.split(r"(?<=[.?!\])])\s+(?=[A-Z\"“])", para):
            if s.strip():
                sentences.append(s.strip())
    rows, cited_all, unknown = [], set(), set()
    clean_paras = []
    for para in reply.split("\n"):
        clean = para
        for m in BRACKET.finditer(para):
            ids = [x.strip() for x in re.split(r"[,;]\s*|\s+and\s+", m.group(1)) if x.strip()]
            if ids == ["none"] or (ids and all(re.fullmatch(r"[A-Za-z_][\w']*", x) for x in ids) and any(x in names for x in ids)):
                clean = clean.replace(m.group(0), "")
        clean_paras.append(re.sub(r"\s+([.,;:?!])", r"\1", clean))
    for i, s in enumerate(sentences, 1):
        cites = []
        for m in BRACKET.finditer(s):
            ids = [x.strip() for x in re.split(r"[,;]\s*|\s+and\s+", m.group(1)) if x.strip()]
            if ids == ["none"]:
                cites.append("none"); continue
            if ids and all(re.fullmatch(r"[A-Za-z_][\w']*", x) for x in ids):
                for x in ids:
                    if x in names:
                        cites.append(x); cited_all.add(x)
                    else:
                        unknown.add(x)
        text = BRACKET.sub(lambda m: "" if all(re.fullmatch(r"[A-Za-z_][\w']*", x.strip()) for x in re.split(r"[,;]\s*", m.group(1)) if x.strip()) else m.group(0), s).strip()
        rows.append({"i": i, "sentence": text, "cites": cites, "kinds": {c: kind(c) for c in cites}})
    # a citation covers the sentences written since the previous citation (the model often cites a group at once)
    pending = []
    for r in rows:
        if r["cites"]:
            r["span"] = " ".join([x["sentence"] for x in pending] + [r["sentence"]])
            for x in pending:
                x["covered_by"] = r["i"]
            pending = []
        else:
            pending.append(r)
    for r in rows:
        r.setdefault("span", r["sentence"])

    L = [f"Citations in {rv.name}, checked against {r1.name}", ""]
    L.append(f"{len(rows)} sentences; {sum(1 for r in rows if r['cites'])} cite something.")
    L.append("")
    L.append("1. Sentences that cite isolated items (final does not use them):")
    hits = [r for r in rows if any(k.startswith("isolated") for k in r["kinds"].values())]
    for r in hits:
        L.append(f"  [{r['i']}] {r['span']}")
        L.append("      isolated: " + ", ".join(c for c, k in r["kinds"].items() if k.startswith("isolated")))
    if not hits:
        L.append("  none")
    L.append("")
    cited_norm = {c.removesuffix("_def") for c in cited_all} | cited_all
    missing = sorted(c for c in core if c not in cited_norm and c.removesuffix("_def") not in cited_norm)
    L.append(f"2. Items of the set final rests on that no sentence cites ({len(missing)} of {len(core)}): " + (", ".join(missing) if missing else "none"))
    L.append("")
    bare = [r for r in rows if not r["cites"] and "covered_by" not in r]
    said_none = [r for r in rows if r["cites"] == ["none"]]
    L.append(f"3a. Sentences marked [none] by the model ({len(said_none)}):")
    L += [f"  [{r['i']}] {r['sentence']}" for r in said_none] or ["  none"]
    L.append(f"3b. Sentences with no citation, not even one given after a later sentence of the same group ({len(bare)}):")
    L += [f"  [{r['i']}] {r['sentence']}" for r in bare] or ["  none"]
    L.append("")
    L.append("4. Cited names the source does not have: " + (", ".join(sorted(unknown)) if unknown else "none"))
    L.append("")
    L.append("Every sentence and what it cites:")
    for r in rows:
        L.append(f"  [{r['i']}] {r['sentence']}")
        for c, k in r["kinds"].items():
            L.append(f"      {c}: {k}")
    out = rv / "citations"; out.mkdir(exist_ok=True)
    (out / "citations.txt").write_text("\n".join(L) + "\n")
    (out / "citations.json").write_text(json.dumps({"rows": rows, "missing": missing, "unknown": sorted(unknown)}, indent=1, ensure_ascii=False))
    (out / "reply_clean.txt").write_text("\n".join(clean_paras).strip() + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
