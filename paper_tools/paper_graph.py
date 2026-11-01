"""Check item 11 of the ten-part method (method_report/hol_paper_parts.md): the end answers the beginning, and every
part keeps the thesis in view. No model call.

  python3 paper_graph.py ESSAY/formal/v14_ten_parts      # the directory holds graph.json, written by the generator

graph.json lists every file (its premises, each with the file it is taken from, if any, and its final as conjuncts),
the declared links (a reply answers an objection by denying one of its premises; an objection attacks a file), the
echo roles (problem, its rejected premise and its judgment, thesis, core, conclusion), and a HOL4 header with the whole
signature. HOL4 (on the Mac mini) then checks, in one theory:
  - every premise taken from another file is the same term as that file's final or the named conjunct (aconv);
  - every declared answer: the reply's final proves the negation of the named premise (metis);
  - every declared attack: the objection's final proves the negation of the attacked file's final (metis);
  - the echo: the thesis file's final and the core's final are the thesis (aconv); the conclusion's final proves the
    thesis, the negation of the problem's rejected premise, and the problem's judgment (metis).
Python then computes which files are in view: the conclusion; the thesis file and the core, when the echo ties them
to the conclusion; any file a file in view takes a premise from; any file a
file in view answers; any objection that attacks a file in view and is answered, with its reply. A file not in view
stands alone. Premises taken from a later file are listed: only the thesis file (a roadmap) may have them, and each
must be proved by a file that comes later. Writes DIR/graph_check/report.txt and DIR/structure.md (part 9).
"""
import json, shutil, sys
from pathlib import Path

HOL = Path("/Users/cy/Desktop/Fun/possibility_calculator/Learn/experiments/moral-reasoning/experiments/data/"
           "thick_training/difficult_advice_v2/cloud_gen/hol")
sys.path.insert(0, str(HOL / "tools"))
from native_check import check  # noqa: E402


def conj(cs):
    return cs[0] if len(cs) == 1 else " /\\ ".join(f"({c})" for c in cs)


def ml(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main(d):
    d = Path(d).resolve()
    g = json.loads((d / "graph.json").read_text())
    files = {f["name"]: f for f in g["files"]}
    order = [f["name"] for f in g["files"]]
    fin = {n: conj(f["final"]) for n, f in files.items()}
    checks = []                                  # (id, kind, ml expression returning bool)
    for f in g["files"]:
        for p in f["premises"]:
            if p["from"]:
                src = files[p["from"]["file"]]
                k = p["from"]["conjunct"]
                want = fin[src["name"]] if k is None else src["final"][k]
                checks.append((f"uses|{src['name']}|{f['name']}|{p['name']}", f"same {ml(p['term'])} {ml(want)}"))
    for a, b, prem in g["answers"]:
        t = next(p["term"] for p in files[b]["premises"] if p["name"] == prem)
        checks.append((f"answers|{a}|{b}|{prem}", f"proves {ml('(' + fin[a] + ') ==> ~(' + t + ')')}"))
    for a, b in g["attacks"]:
        checks.append((f"attacks|{a}|{b}|", f"proves {ml('(' + fin[a] + ') ==> ~(' + fin[b] + ')')}"))
    e = g["echo"]
    prob = files[e["problem"]]
    rej = next(p["term"] for p in prob["premises"] if p["name"] == e["rejected"])
    jud = next(p["term"] for p in prob["premises"] if p["name"] == e["judgment"])
    th, conc = fin[e["thesis"]], fin[e["conclusion"]]
    checks += [("echo|thesis=core||", f"same {ml(th)} {ml(fin[e['core']])}"),
               ("echo|conclusion=>thesis||", f"proves {ml('(' + conc + ') ==> (' + th + ')')}"),
               ("echo|conclusion=>not rejected||", f"proves {ml('(' + conc + ') ==> ~(' + rej + ')')}"),
               ("echo|conclusion=>judgment||", f"proves {ml('(' + conc + ') ==> (' + jud + ')')}")]
    src = g["header"]
    src += ('fun out s = TextIO.print ("GRAPH|" ^ s ^ "\\n");\n'
            "fun tm s = Parse.Term [QUOTE s];\n"
            "fun same a b = (aconv (tm a) (tm b)) handle _ => false;\n"
            "fun proves s = ((ignore (prove (tm s, metis_tac [])); true) handle _ => false);\n")
    for i, (cid, expr) in enumerate(checks):
        src += f"val _ = out ({ml(cid)} ^ \"|\" ^ Bool.toString ({expr}));\n"
    src += "\nTheorem final:\n  T\nProof\n  simp []\nQED\n\nval _ = export_theory ();\n"
    out = d / "graph_check"
    if out.is_dir():
        shutil.rmtree(out)
    out.mkdir()
    (out / "source.sml").write_text(src)
    r = check(out / "source.sml", out / "native_check", "hol4", "mini", timeout=900)
    log = (out / "native_check" / "native.log").read_text() if (out / "native_check" / "native.log").exists() else ""
    res = {}
    for line in log.splitlines():
        if "GRAPH|" in line:                     # metis may print its progress on the same line first
            parts = line.split("GRAPH|", 1)[1].split("|")
            res["|".join(parts[0:4])] = parts[4].strip() == "true"
    missing = [cid for cid, _ in checks if cid not in res]

    # which files are in view
    ok = lambda cid: res.get(cid, False)
    uses = [(c.split("|")[1], c.split("|")[2]) for c, _ in checks if c.startswith("uses|") and ok(c)]
    answers = [(a, b) for a, b, p in g["answers"] if ok(f"answers|{a}|{b}|{p}")]
    attacks = [(a, b) for a, b in g["attacks"] if ok(f"attacks|{a}|{b}|")]
    view = {e["conclusion"]}
    if ok("echo|thesis=core||") and ok("echo|conclusion=>thesis||"):
        view |= {e["core"], e["thesis"]}         # the thesis file and the core are tied to the conclusion by the echo
    changed = True
    while changed:
        changed = False
        new = set()
        new |= {src_ for src_, user in uses if user in view}
        new |= {b for a, b in answers if a in view}
        for a, b in attacks:
            if b in view:
                reps = [x for x, y in answers if y == a]
                if reps:
                    new |= {a, *reps}
        if not new <= view:
            view |= new
            changed = True
    alone = [n for n in order if n not in view]
    forward = [(src_, user) for src_, user in uses if order.index(src_) > order.index(user)]
    bad_forward = [(s, u) for s, u in forward if u != e["thesis"]]

    L = [f"HOL4: {r.get('status')} exit {r.get('exit_code')}", ""]
    L += [f"{'ok  ' if res.get(cid) else 'FAIL'} {cid}" for cid, _ in checks if cid in res]
    if missing:
        L += ["", "no result (see graph_check/native_check/native.log):"] + [f"  {c}" for c in missing]
    L += ["", "echo (11a): " + ("passed" if all(ok(c) for c, _ in checks if c.startswith("echo|")) else "FAILED"),
          "thesis in view (11b): " + ("every file" if not alone else "NOT in view: " + ", ".join(alone)),
          "premises taken from later files: " + (", ".join(f"{u} <- {s}" for s, u in forward) or "none")
          + ("" if not bad_forward else "; only the thesis file may: " + ", ".join(f"{u} <- {s}" for s, u in bad_forward))]
    (out / "report.txt").write_text("\n".join(L) + "\n")

    S = ["# Structure (part 9): the file graph", "", "Generated by `papers/tools/paper_graph.py`. "
         "An arrow `A -> B` means B takes A's final (or one conjunct of it) as a premise; `R answers O` means R's final denies one of O's premises; "
         "`O attacks X` means O's final denies X's final.", ""]
    for n in order:
        f = files[n]
        ins = sorted({s for s, u in uses if u == n}, key=order.index)
        outs = sorted({u for s, u in uses if s == n}, key=order.index)
        S.append(f"- **{n}** ({f['part']}): {f['title']}")
        if ins: S.append(f"  - takes from: {', '.join(ins)}")
        if outs: S.append(f"  - used by: {', '.join(outs)}")
        for a, b in answers:
            if a == n: S.append(f"  - answers: {b}")
            if b == n: S.append(f"  - answered by: {a}")
        for a, b in attacks:
            if a == n: S.append(f"  - attacks: {b}")
    (d / "structure.md").write_text("\n".join(S) + "\n")
    print("\n".join(L))
    return 0 if not missing and not alone and not bad_forward and all(res.values()) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
