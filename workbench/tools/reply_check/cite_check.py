"""Check a round-2 reply's theorem citations against the round-1 argument. No LLM call.

  python3 tools/reply_check/cite_check.py runs/ROUND2_RUN runs/ROUND1_RUN       # writes ROUND2_RUN/cite_check/

The reply cites round-1 theorems by name, like [final]. Each cited theorem is read in stiff plain English by
plain_english.py (the formula's structure, the model's notation comments for words). An NLI cross-encoder on the mini
(nli_pairs.py) then scores, for each sentence and each theorem it cites:
  says    names + sentence => each conclusion of the theorem       (does the sentence state it?)
          controls: the same with the conclusion negated; names alone => the conclusion
  backed  names + the whole theorem => the sentence                 (does the theorem support the sentence?)
          control: the best score from a theorem the sentence does not cite
Coverage lists every conclusion of the final theorem and the best "says" score any sentence citing it reached.
"""
import argparse, json, re, shlex, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from plain_english import Plain, sentence                        # noqa: E402
from gloss_claims import glosses, split_imp                       # noqa: E402

CITE = re.compile(r"\s*\[([A-Za-z_][\w']*(?:\s*,\s*[A-Za-z_][\w']*)*)\]")
NEG = "It is not true that "


def read_theorems(run, use_names=True, bare=False):
    nc = run / "native_check"
    ast = json.loads((nc / "kernel_ast.json").read_text())
    notation, views = glosses((nc / "source.sml").read_text())
    defs = {d["name"]: d for d in ast["definitions"]}
    r = Plain(notation, views, defs, use_names=use_names, bare=bare)
    thms = {}
    for t in ast["theorem_values"]:
        if t["name"] in defs or t["name"].endswith("_def"):
            continue
        ants, cons = split_imp(t["conclusion"])
        thms[t["name"]] = {"premises": [sentence(r.render(p)) for p in ants], "conclusions": [sentence(r.render(c)) for c in cons]}
    names = {}
    for line in (r.intro if r.use_names else []):
        label = next(v for v in r.names.values() if line.startswith(v + " "))
        names.setdefault(label, []).append(line)
    return thms, names


def glossary(names, *texts):
    used = [n for n in names if any(re.search(r"\b" + re.escape(n) + r"\b", t) for t in texts)]
    return "\n".join(l for n in used for l in names[n])


def whole(th):
    text = " ".join(th["conclusions"])
    if th["premises"]:
        text = "Suppose that " + "; ".join(p[0].lower() + p[1:-1] for p in th["premises"]) + ". Then: " + text
    return text


def negate(text, names):
    if text.startswith(NEG):
        s = text[len(NEG):]; return s[0].upper() + s[1:]
    return NEG + (text if any(text.startswith(n + " ") for n in names) else text[0].lower() + text[1:])


def join(*parts):
    return "\n\n".join(p for p in parts if p)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("round2"); ap.add_argument("round1")
    ap.add_argument("--host", default="mini"); ap.add_argument("--final", default="final")
    ap.add_argument("--no-names", action="store_true", help="write each argument term out in full instead of 'View 3'")
    ap.add_argument("--bare", action="store_true", help="each argument term is the model's own comment, quoted")
    a = ap.parse_args()
    r2, r1 = Path(a.round2), Path(a.round1)
    thms, names = read_theorems(r1, use_names=not a.no_names, bare=a.bare)
    reply = (r2 / "response.txt").read_text().strip()
    sents = [s.strip() for p in reply.split("\n") for s in re.split(r"(?<=[.?!])\s+(?=[A-Z\"“])", p) if s.strip()]
    cited, unknown, pairs = [], [], []
    for i, s in enumerate(sents):
        refs = [n.strip() for m in CITE.finditer(s) for n in m.group(1).split(",")]
        plain = CITE.sub("", s).strip()
        known = [n for n in refs if n in thms]
        unknown += [n for n in refs if n not in thms]
        prev = CITE.sub("", sents[i - 1]).strip() if i else ""
        cited.append({"i": i, "sentence": plain, "cites": known})
        for n in known:
            for k, c in enumerate(thms[n]["conclusions"]):
                g = glossary(names, c)
                base = {"i": i, "theorem": n, "conclusion": k}
                pairs.append({**base, "test": "says", "premise": join(g, plain), "hypothesis": c})
                pairs.append({**base, "test": "says_negated", "premise": join(g, plain), "hypothesis": negate(c, names)})
                pairs.append({**base, "test": "says_with_previous", "premise": join(g, prev + " " + plain), "hypothesis": c})
                pairs.append({**base, "test": "says_with_previous_negated", "premise": join(g, prev + " " + plain), "hypothesis": negate(c, names)})
                if g:
                    pairs.append({**base, "test": "says_names_only", "premise": g, "hypothesis": c})
            w = whole(thms[n])
            pairs.append({"i": i, "theorem": n, "test": "backed", "premise": join(glossary(names, w), w), "hypothesis": plain})
            for other, th in thms.items():
                if other not in known:
                    w2 = whole(th)
                    pairs.append({"i": i, "theorem": other, "test": "backed_by_uncited", "premise": join(glossary(names, w2), w2), "hypothesis": plain})
    out = r2 / ("cite_check_bare" if a.bare else "cite_check_nonames" if a.no_names else "cite_check"); out.mkdir(exist_ok=True)
    (out / "pairs.json").write_text(json.dumps(pairs, indent=1, ensure_ascii=False))
    (out / "theorems_plain.json").write_text(json.dumps({"names": names, "theorems": thms}, indent=1, ensure_ascii=False))
    remote = f"thick_training/cite_check/{r2.name}/{out.name}"
    subprocess.run(["ssh", a.host, f"mkdir -p {shlex.quote(remote)}"], check=True)
    subprocess.run(["scp", "-q", str(HERE / "nli_pairs.py"), str(out / "pairs.json"), f"{a.host}:{remote}/"], check=True)
    subprocess.run(["ssh", a.host, f"cd {shlex.quote(remote)} && HF_HUB_OFFLINE=1 ~/negbert-venv/bin/python nli_pairs.py pairs.json nli.json 2>&1 | tail -1"], check=True)
    subprocess.run(["scp", "-q", f"{a.host}:{remote}/nli.json", str(out)], check=True)
    res = json.loads((out / "nli.json").read_text())["results"]

    def get(i, n, test, k=None):
        return [r for r in res if r["i"] == i and r["theorem"] == n and r["test"] == test and (k is None or r.get("conclusion") == k)]
    rows, L = [], []
    for c in cited:
        if not c["cites"]:
            continue
        L.append(f'[{c["i"]}] {c["sentence"]}')
        for n in c["cites"]:
            backed = get(c["i"], n, "backed")[0]["entail"]
            uncited = max((r["entail"] for r in res if r["i"] == c["i"] and r["test"] == "backed_by_uncited"), default=0)
            L.append(f'    cites {n}: backed {backed:.2f} (best uncited theorem {uncited:.2f})')
            for k, concl in enumerate(thms[n]["conclusions"]):
                s = get(c["i"], n, "says", k)[0]["entail"]; sn = get(c["i"], n, "says_negated", k)[0]["entail"]
                so = get(c["i"], n, "says_names_only", k); so = so[0]["entail"] if so else None
                sp = get(c["i"], n, "says_with_previous", k)[0]["entail"]; spn = get(c["i"], n, "says_with_previous_negated", k)[0]["entail"]
                rows.append({"i": c["i"], "theorem": n, "conclusion": concl, "says": s, "says_negated": sn, "names_only": so,
                             "says_with_previous": sp, "says_with_previous_negated": spn,
                             "backed": backed, "best_uncited": uncited})
                L.append(f'      says "{concl}": {s:.2f}   negated {sn:.2f}' + (f"   names only {so:.2f}" if so is not None else "")
                         + f"   | with previous sentence {sp:.2f}, negated {spn:.2f}")
    L.append("")
    L.append(f"Coverage of {a.final}:")
    for k, concl in enumerate(thms.get(a.final, {}).get("conclusions", [])):
        hits = [r for r in rows if r["theorem"] == a.final and r["conclusion"] == concl]
        best = max(hits, key=lambda r: r["says"]) if hits else None
        L.append(f'  "{concl}": ' + (f'cited by sentence {best["i"]}, says {best["says"]:.2f}, negated {best["says_negated"]:.2f}' if best else "no sentence cites it"))
    never = [n for n in thms if not any(n in c["cites"] for c in cited)]
    L.append("Theorems no sentence cites: " + (", ".join(never) if never else "none"))
    if unknown:
        L.append("Cited names that are not round-1 theorems: " + ", ".join(sorted(set(unknown))))
    (out / "cite_check.json").write_text(json.dumps({"sentences": cited, "rows": rows, "unknown": unknown}, indent=1, ensure_ascii=False))
    (out / "cite_check.txt").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
