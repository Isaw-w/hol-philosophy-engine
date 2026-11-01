"""Find what an essay's sentences say that its argument does not need. Code only, no model.

  python3 surplus_check.py ESSAY            # writes ESSAY/prose/surplus_report.md
  python3 surplus_check.py --test           # the known cases of 2026-10-21 must all be caught

An argument (Besnard and Hunter 2001; Elements of Argumentation, 2008) is a consistent, minimal set of premises that
entails its claim; the HOL4 gate checks that for the formulas. It cannot see the English. Each constant's gloss in
source.sml is free text, so a gloss can say more than any premise needs. A word in a gloss is *supported* if it is in
the constant's own name, in the gloss of a constant that shares a statement with it, or in an English quotation of a
text constant that shares a statement with it. The detectors:

  contrast      "not merely / rather than / as opposed to / instead of / not only X", where X is unsupported
  side-claim    a gloss that carries a quotation token but is not a plain attribution ("Name writes that [Qn]"),
                so it makes a claim and quotes someone in one breath
  relative      a relative clause ("that / which / who ...") on a noun, with unsupported words
  coordination  "X and Y" where Y is unsupported and X is not
  restates      the part after a colon repeats the glosses of the premises that already imply the constant
                (half or more of its words are in those glosses)

A word can be unsupported because its source is in Chinese with no English yet; such findings are marked "check
against the source". Also listed: words the blind translation and the polish added to each sentence.
"""
import json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prose_pipeline import parse_translation, num

STOP = set("""a an the and or but if then so that this these those it its it's they them their there here of in on at
to for from by with without as than into onto over under about after before between through during within upon
is are was were be been being has have had do does did not no nor any every each all some such one ones only also
either neither both whether which who whom whose what when where while because though although even yet still
can could may might must shall should will would i we you he she his her our my me us your himself herself itself
themselves own same other others another more most less least much many very just following hold holds true false
x t thus let suppose whenever""".split())
ATTRIBUTION = re.compile(r"^(?:[A-Z][a-zà-öø-ÿ]*[A-Z]?[a-zà-öø-ÿ]+(?:-[A-Z][a-zà-öø-ÿ]+)?(?: [A-Z][a-zà-öø-ÿ]*[A-Z]?[a-zà-öø-ÿ]+(?:-[A-Z][a-zà-öø-ÿ]+)?)*(?: and [A-Z][a-zà-öø-ÿ]*[A-Z]?[a-zà-öø-ÿ]+(?:-[A-Z][a-zà-öø-ÿ]+)?)?(?:'s remedy)?|the remedy proposed in [^,]+?)"
                         r"(?:, [^,]+,)? (?:writes|write|wrote|records|warns|argue|argues|holds|reports|cites|explains|names|gives|"
                         r"takes|take|propose|proposes|describes|asks|is)\b")
CONTRAST = re.compile(r"\b(?:not merely|rather than|as opposed to|instead of|not only)\s+([^,;:)]+)")
RELATIVE = re.compile(r"\b([a-z]+)\s+(?:that|which|who|whom|whose)\s+([^,;:()]+)")
COORD = re.compile(r"\b([a-z]+)\s+and\s+([a-z]+)\b")
NOT_NOUNS = set("writes wrote records warns argue argues holds reports cites explains believe believes know knows "
                "says say think thinks deny denies so such is are was were be the a an and or of to".split())


def stem(w):
    w = w.lower().strip("'’")
    w = re.sub(r"['’]s$", "", w)
    for suf, rep in (("ies", "y"), ("ied", "y"), ("ing", ""), ("ed", ""), ("es", ""), ("s", ""), ("ly", "")):
        if len(w) > len(suf) + 3 and w.endswith(suf):
            w = w[: -len(suf)] + rep
            break
    return w[:-1] if len(w) > 4 and w.endswith("e") else w


def words(s):
    s = re.sub(r"\[Q\d+\]", " ", s)
    s = re.sub(r"\\emph\{(.*?)\}", r"\1", s)
    return {stem(w) for w in re.findall(r"[A-Za-z][A-Za-z'’-]*|\d{3,4}", s) if w.lower() not in STOP and len(w) > 1}


def name_words(name):
    return {stem(w) for w in re.findall(r"[A-Z][a-z]+|[a-z]+", name)}


def glosses(src):
    return {m[1]: m[2] for m in re.finditer(r"\(\*\s*([A-Z]\w*)(?:\s+\w)?\s*:\s*(.*?)\s*\*\)", src)}


def statements(src):
    return re.findall(r"new_axiom\s*\(\s*\"\w+\"\s*,\s*``(.*?)``", src, re.S) + \
        re.findall(r"^Theorem\s+\w+:\s*\n(.*?)\nProof", src, re.S | re.M)


def collect(prose):
    gl, co, implied_by = {}, {}, {}
    pars = sorted([p for p in prose.glob("s*/p*") if p.is_dir()], key=lambda p: (num(p.parent), num(p)))
    for par in pars:
        src = (par / "source.sml").read_text()
        g = glosses(src)
        gl.update(g)
        for st in statements(src):
            names = {c for c in g if re.search(rf"\b{c}\b", st)}
            for c in names:
                co.setdefault(c, set()).update(names - {c})
            m = re.match(r"\s*(?:!\w+\.\s*)?(.*)==>\s*(\w+)\s+\w+\s*$", st.strip(), re.S)
            if m and "==>" not in m[1]:
                implied_by.setdefault(m[2], set()).update(c for c in g if re.search(rf"\b{c}\b", m[1]))
    return pars, gl, co, implied_by


def findings(gl, co, implied_by, tokens):
    is_text = {c: bool(re.search(r"\[Q\d+\]", g)) for c, g in gl.items()}
    out = []
    for c, g in gl.items():
        support, chinese = set(name_words(c)), False
        for d in co.get(c, ()):
            if is_text.get(d):
                for t in re.findall(r"\[Q\d+\]", gl[d]):
                    if t in tokens:
                        support |= words(tokens[t])
                    else:
                        chinese = True
            elif d in gl:
                support |= words(gl[d]) | name_words(d)
        note = " (source not yet in English: check against the source)" if chinese else ""
        if is_text[c]:
            if not ATTRIBUTION.match(g):
                out.append((c, "side-claim", f"makes a claim and carries a quotation: \"{g}\""))
            continue
        for m in CONTRAST.finditer(g):
            un = sorted(words(m[1]) - support)
            if un:
                out.append((c, "contrast", f"\"{m.group(0).strip()}\": {un} unsupported{note}"))
        for m in RELATIVE.finditer(g):
            if m[1] in NOT_NOUNS:
                continue
            un = sorted(words(m[2]) - support)
            if un:
                out.append((c, "relative", f"\"{m[1]} ... {m[2].strip()}\": {un} unsupported{note}"))
        for m in COORD.finditer(g):
            a, b = words(m[1]), words(m[2])
            if b and not (b & support) and (a & support or not a):
                out.append((c, "coordination", f"\"{m[1]} and {m[2]}\": {sorted(b)} unsupported{note}"))
        if ":" in g and c in implied_by:
            tail = words(g.split(":", 1)[1])
            prem = set().union(*(words(gl[d]) for d in implied_by[c] if d in gl)) if implied_by[c] else set()
            if tail and len(tail & prem) * 2 >= len(tail):
                out.append((c, "restates", f"after the colon it repeats the premises that imply it "
                                           f"({', '.join(sorted(implied_by[c]))}): {sorted(tail & prem)}"))
    return out


def main(essay):
    prose = Path(essay).resolve() / "prose"
    polish = json.loads((prose / "polish.json").read_text()) if (prose / "polish.json").exists() else {}
    pars, gl, co, implied_by = collect(prose)
    found = findings(gl, co, implied_by, polish.get("tokens", {}))
    rep = ["# Surplus report", "", "Made by `papers/tools/surplus_check.py` (code only). Candidates for the user to decide.", "",
           f"{len(found)} findings in {len({c for c, _, _ in found})} of {len(gl)} glosses.", "",
           "## Glosses", "", "| Constant | Kind | Finding |", "|---|---|---|"]
    rep += [f"| `{c}` | {k} | {t.replace('|', '/')} |" for c, k, t in found]
    added = {"translation": [], "polish": []}
    for par in pars:
        trans = parse_translation(par.parent / "translation.txt") if (par.parent / "translation.txt").exists() else {}
        mech = {l.split(". ", 1)[0]: l.split(". ", 1)[1] for l in (par / "mechanical.txt").read_text().split("\n\n") if l.strip()}
        for lab, m in mech.items():
            base = words(m)
            if lab in trans and words(trans[lab]) - base:
                added["translation"].append(f"- {lab}: {sorted(words(trans[lab]) - base)}")
            for old, new in polish.get("replace", {}).get(lab, []):
                if words(new) - base:
                    added["polish"].append(f"- {lab}: {sorted(words(new) - base)}")
    rep += ["", "## Words the blind translation added", ""] + (added["translation"] or ["none"])
    rep += ["", "## Words the polish added", ""] + (added["polish"] or ["none"])
    (prose / "surplus_report.md").write_text("\n".join(rep) + "\n")
    print("\n".join(rep[4:]))


def test():
    """The five surpluses found on 2026-10-21 must all be caught, each by its kind."""
    gl = {
        "Authority": "x has genuine authority, and not merely formal force, for those who share the life in which it is practised",
        "MakesSense": "x makes sense by the considered standards of the shared life in which it is practised",
        "Idle": "the tradition's critique of x was idle talk that moved no one",
        "LineageOut": "a lineage that kept to the sage's example stayed out of x for generations",
        "StopAloneCost": "a household that gives up x alone makes its daughters seem unfit to be women and wives",
        "QianStanding": "Qian Yong writes that [Q16]",
        "OthersDo": "each household keeps x because the other households keep it, and is ashamed not to",
        "KnewCost": "those who keep x know the pain it causes those whom it burdens",
        "Trap": "x is held in place by a coordination trap: each household keeps x, though it sees the pain x causes, because the others keep it and a household that stops alone pays for stopping",
        "Abandon": "a shared life's moral values are abandoned wholesale, which Sleat denies that the radical realists' arguments justify: [Q27]",
        "DrawsOnValues": "the critique of x draws on the shared life's own moral values",
        "CritiqueKept": "the critique of x is kept",
    }
    co = {"Authority": {"MakesSense"}, "MakesSense": {"Authority"}, "Idle": {"LineageOut"}, "LineageOut": {"Idle"},
          "StopAloneCost": {"QianStanding", "Trap"}, "Trap": {"OthersDo", "StopAloneCost", "KnewCost"},
          "OthersDo": {"Trap"}, "KnewCost": {"Trap"}, "Abandon": {"DrawsOnValues", "CritiqueKept"},
          "DrawsOnValues": {"Abandon", "CritiqueKept"}, "CritiqueKept": {"Abandon", "DrawsOnValues"}}
    implied_by = {"Trap": {"OthersDo", "StopAloneCost", "KnewCost"}}
    found = {(c, k) for c, k, _ in findings(gl, co, implied_by, {})}
    want = {("Authority", "contrast"), ("Idle", "relative"), ("StopAloneCost", "coordination"),
            ("Trap", "restates"), ("Abandon", "side-claim")}
    missed = want - found
    print("caught:", sorted(want & found)); print("missed:", sorted(missed)); print("also flagged:", sorted(found - want))
    sys.exit(1 if missed else 0)


if __name__ == "__main__":
    test() if sys.argv[1] == "--test" else main(sys.argv[1])
