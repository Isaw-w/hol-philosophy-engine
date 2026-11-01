"""Turn an essay into prose by the user's method: every paragraph is a minimal argument built in HOL; then
HOL -> mechanical English (the renderer, no model) -> natural language (a fresh agent with no background) -> a light,
logged polish. The AI writes no sentence of the essay directly.

  python3 prose_pipeline.py render   ESSAY/prose/s3/p2   # HOL4 check, mechanical English (labelled 3.2.1, 3.2.2, ...)
  python3 prose_pipeline.py check    ESSAY/prose/s3/p2   # the gate (Z3 engine): every premise needed, none idle, consistent
  python3 prose_pipeline.py prompt   ESSAY/prose/s3      # one blind-agent prompt for all paragraphs of a section
  python3 prose_pipeline.py assemble ESSAY [PROSE_DIR]   # translations + polish.json -> PROSE_DIR/abstract.tex, body.tex

Layout: ESSAY/prose/s<k>/p<j>/source.sml, with statements named p<k>_<j>_<nn> in reading order (premises as axioms,
the paragraph's conclusion as the last Theorem) and a Theorem `final` restating the conclusion for the checks.
Section s0 holds the abstract. The blind agent's answer for a section is saved verbatim as s<k>/translation.txt.
prose/polish.json lists the only edits allowed after translation: "replace" (label -> [[old, new], ...]),
"tokens" ([Q1] -> verbatim quotation), "cite" (label -> \\autocite{...}), "headings" (section number -> title),
"sections" (optional reading order: [heading, ["s1/p1", ...]] for the body, overriding folder order and "headings"),
"math" (lone variable letters to set as $s$).
Every edit is written to prose/polish_log.txt.
"""
import json, re, shutil, subprocess, sys
from pathlib import Path

import os
HOL = Path(os.environ.get("HOLVERIFY_WORKBENCH", Path(__file__).resolve().parent.parent / "workbench"))
PROMPT = ("Convert these mechanical sentences into natural language. Keep each label and each bracketed token, "
          "and keep the meaning of each sentence exactly.\n\n")
NAME = re.compile(r"^p(\d+)_(\d+)_(\d+)$")


def label(name):
    m = NAME.match(name)
    return f"{int(m[1])}.{int(m[2])}.{int(m[3])}"


def num(p):
    return int(re.sub(r"\D", "", p.name))


def render(par):
    par = Path(par).resolve()
    nc = par / "native_check"
    if nc.exists() and (not (nc / "source.sml").exists() or (nc / "source.sml").read_text() != (par / "source.sml").read_text()):
        shutil.rmtree(nc)                      # the source changed since HOL4 last ran: run it again
        shutil.rmtree(par / "gloss_claims", ignore_errors=True)
    if not (par / "native_check").exists():
        sys.path.insert(0, str(HOL / "tools"))
        from native_check import check
        r = check(par / "source.sml", par / "native_check", "hol4", "mini", timeout=600)
        if r.get("status") != "processed" or r.get("exit_code") != 0:
            raise SystemExit(f"HOL4 failed in {par}: {r.get('status')} {r.get('exit_code')}")
    log = (par / "native_check" / "native.log").read_text()
    if "val final =" not in log:
        raise SystemExit(f"{par}: HOL4 did not prove final")
    subprocess.run([sys.executable, "tools/reply_check/plain_english.py", str(par), "--no-names"], cwd=HOL,
                   check=True, capture_output=True)
    text = (par / "gloss_claims" / "plain_nonames.txt").read_text()
    blocks = dict(re.findall(r"Theorem (\w+):\n((?:  .*\n?)+)", text))
    order = re.findall(r"^\s*(?:val\s+\w+\s*=\s*new_axiom\s*\(\s*\"|Theorem\s+)(p\d+_\d+_\d+)",
                       (par / "source.sml").read_text(), re.M)
    missing = [n for n in order if n not in blocks]
    if missing:
        raise SystemExit(f"{par}: not rendered: {missing}")
    lines = [f"{label(n)}. " + " ".join(l.strip() for l in blocks[n].strip().splitlines()) for n in order]
    (par / "mechanical.txt").write_text("\n\n".join(lines) + "\n")
    print("\n\n".join(lines))


def check(par):
    """the gate, by the workbench's Z3 engine: every premise needed (in every smallest support of some conclusion,
    the lists complete), none isolated, consistent, no hard flaw"""
    par = Path(par).resolve()
    for tool in ("hidden_premises", "isolated_parts", "argument_checks", "z3_engine"):
        if (par / tool).is_dir():
            shutil.rmtree(par / tool)
        (par / f"{tool}.out").unlink(missing_ok=True)
    r = subprocess.run([sys.executable, "tools/reply_check/z3_engine.py", str(par)], cwd=HOL, capture_output=True, text=True)
    (par / "z3_engine.out").write_text(r.stdout + r.stderr)
    z = json.loads((par / "z3_engine" / "z3_engine.json").read_text())
    concs = z["conclusions"]
    needed = {s_: any(c["supports"] and all(s_ in sup for sup in c["supports"]) for c in concs) for s_ in z["starts"]}
    flaws = {k: z[k] for k in ("takes_truth_value", "text_contents", "creative", "collapse", "explosion") if z.get(k)}
    report = {"premises": len(needed), "not_needed": [s_ for s_, v in needed.items() if not v],
              "unused_axioms": len(z["isolated"]), "consistent": z["consistent"] == "consistent",
              "lists_complete": all(c.get("complete") for c in concs), "hard_flaws": flaws,
              "near_restatements": z.get("circular") or ""}
    (par / "gate.json").write_text(json.dumps(report, indent=1))
    ok = (report["premises"] > 0 and not report["not_needed"] and report["unused_axioms"] == 0 and report["consistent"]
          and report["lists_complete"] and not flaws)
    print(f"{par.parent.name}/{par.name}: {'PASS' if ok else 'CHECK'} {json.dumps(report)}")


def prompt(sec):
    sec = Path(sec).resolve()
    paras = sorted([p for p in sec.glob("p*") if p.is_dir()], key=num)
    body = "\n\n".join((p / "mechanical.txt").read_text().strip() for p in paras)
    (sec / "prompt.txt").write_text(PROMPT + body + "\n")
    print(PROMPT + body)


def parse_translation(path):
    out = {}
    for m in re.finditer(r"^\s*\**(\d+\.\d+\.\d+)\.?\**\s+(.*?)(?=^\s*\**\d+\.\d+\.\d+\.?\**\s|\Z)", path.read_text(), re.M | re.S):
        out[m[1]] = " ".join(m[2].split())
    return out


def reading_order(prose, polish):
    """(heading or None, paragraph dir) in reading order. polish["sections"], if given, is a list of
    [heading, ["s1/p1", ...]] for the body (the abstract s0 always comes first); otherwise folder order."""
    if "sections" in polish:
        out = [(None, p) for p in sorted([p for p in (prose / "s0").glob("p*") if p.is_dir()], key=num)]
        for heading, pars in polish["sections"]:
            out += [(heading if i == 0 else None, prose / p) for i, p in enumerate(pars)]
        return out
    out = []
    for sec in sorted([s for s in prose.glob("s*") if s.is_dir()], key=num):
        k = num(sec)
        heading = polish.get("headings", {}).get(str(k)) if k else None
        out += [(heading if i == 0 else None, p) for i, p in
                enumerate(sorted([p for p in sec.glob("p*") if p.is_dir()], key=num))]
    return out


def assemble(essay, prose_dir="prose"):
    prose = Path(essay).resolve() / prose_dir     # e.g. "prose_v5" for a later version of the prose
    polish = json.loads((prose / "polish.json").read_text()) if (prose / "polish.json").exists() else {}
    log, abstract, body = [], [], []
    for heading, par in reading_order(prose, polish):
        sec = par.parent
        sentences = parse_translation(sec / "translation.txt")
        k = num(sec)
        if heading:
            body.append(f"\\section{{{heading}}}\n")
        labels = [l.split(". ", 1)[0] for l in (par / "mechanical.txt").read_text().split("\n\n") if l.strip()]
        text = []
        for lab in labels:
            if lab not in sentences:
                raise SystemExit(f"{sec.name}: the translation lost label {lab}")
            s = sentences[lab]
            for old, new in polish.get("replace", {}).get(lab, []):
                if old not in s:
                    raise SystemExit(f"{lab}: polish text not found: {old!r}")
                s = s.replace(old, new); log.append(f"{lab}: {old!r} -> {new!r}")
            for v in polish.get("math", []):     # a lone variable letter, not the t of "can't"
                s2 = re.sub(rf"(?<![\w'’$\\]){v}(?![\w$])", f"${v}$", s)
                if s2 != s:
                    s = s2; log.append(f"{lab}: {v} -> ${v}$")
            for tok, new in polish.get("tokens", {}).items():
                if tok in s:
                    s = s.replace(tok, new); log.append(f"{lab}: {tok} -> verbatim quotation")
            cite = polish.get("cite", {}).get(lab)
            if cite:
                s = re.sub(r"([.?!])$", " " + cite.replace("\\", "\\\\") + r"\1", s); log.append(f"{lab}: citation {cite}")
            text.append(s)
        (abstract if k == 0 else body).append(" ".join(text) + "\n")
    (prose / "abstract.tex").write_text("\n".join(abstract))
    (prose / "body.tex").write_text("\n".join(body))
    (prose / "polish_log.txt").write_text("\n".join(log) + "\n")
    print(f"abstract: {len(abstract)} paragraphs; body: {len(body)} blocks; {len(log)} polish edits logged")


if __name__ == "__main__":
    {"render": render, "check": check, "prompt": prompt, "assemble": assemble}[sys.argv[1]](*sys.argv[2:])
