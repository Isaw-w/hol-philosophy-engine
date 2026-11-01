"""Verify any argument written in HOL4. No model call.

    holverify ARGUMENT.sml [ARGUMENT.sml ...]          # verify each argument, print a verdict, write a report
    holverify ARGUMENT.sml --theorem NAME              # the conclusion is theorem NAME (default: `final`)
    holverify ARGUMENT.sml --host local                # run HOL4 on this machine instead of over ssh
    holverify ARGUMENT.sml --json                      # print the verdicts as JSON

An argument is a HOL4 theory: premises as axioms (`new_axiom`) or as the hypotheses of the conclusion, and the
conclusion as a theorem. The verdict follows Besnard and Hunter (Elements of Argumentation, 2008): an argument is a
set of premises that is consistent, entails its claim, and is minimal, so that no premise can be dropped. Checks:

  proved        HOL4 proves the conclusion from the premises
  consistent    the premises can all be true together (Z3; an inconsistency is replayed in HOL4)
  minimal       every premise is needed: it lies in every smallest set of premises that gives some part of the
                conclusion, and the list of smallest sets is complete
  no idle axiom no axiom is cut off from the conclusion
  no hard flaw  none of the flaws the Z3 engine detects (contents given as text, creative definitions, collapse,
                explosion, a constant that takes a truth value without a definition)

Each argument gets a folder OUT/<name>/ with the source, HOL4's log, the Z3 engine's report, the plain English
reading (from the `(* Name : gloss *)` comments, when the source has them), report.md and verdict.json.

Settings (command line, or the environment):
  --host / HOLVERIFY_HOST                ssh host that runs HOL4, or `local` (default: mini)
  --hol4 / HOLVERIFY_HOL4                path of the `hol` binary on that host
  --remote-dir / HOLVERIFY_REMOTE_DIR    working folder on the host (default: thick_training/native_hol_checks)
  --z3 local|host                        where the Z3 engine runs (default: local when the z3 package is installed)
  --remote-python / HOLVERIFY_REMOTE_PYTHON   Python with z3-solver on the host, for --z3 host
"""
import argparse, json, os, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORKBENCH = Path(os.environ.get("HOLVERIFY_WORKBENCH", ROOT / "workbench"))
TOOLS = WORKBENCH / "tools"

FLAWS = ("takes_truth_value", "text_contents", "creative", "collapse", "explosion")


def with_final(text, theorem):
    """The Z3 engine reads the conclusion from a theorem called `final`. If the conclusion has another name, restate
    it as `final` (proved from the named theorem), before export_theory if the source has it."""
    if theorem == "final":
        if not re.search(r"^\s*Theorem\s+final\s*:", text, re.M) and "\"final\"" not in text:
            names = re.findall(r"^\s*Theorem\s+(\w+)\s*:", text, re.M)
            if not names:
                raise SystemExit("no theorem called `final`, and no `Theorem NAME:` to take as the conclusion; "
                                 "use --theorem NAME")
            theorem = names[-1]
            print(f"  no theorem `final`: taking the last theorem, {theorem}, as the conclusion")
        else:
            return text
    m = re.search(rf"^\s*Theorem\s+{re.escape(theorem)}\s*:\s*\n(.*?)^\s*Proof\b", text, re.M | re.S)
    if not m:
        raise SystemExit(f"no `Theorem {theorem}:` block in the source")
    block = f"\nTheorem final:\n  {m.group(1).strip()}\nProof\n  metis_tac [{theorem}]\nQED\n"
    end = re.search(r"^\s*val\s+_\s*=\s*export_theory", text, re.M)
    return text[:end.start()] + block + "\n" + text[end.start():] if end else text + block


def run_hol4(run, host, timeout):
    sys.path.insert(0, str(TOOLS))
    from native_check import check
    r = check(run / "source.sml", run / "native_check", "hol4", host, timeout=timeout)
    log_path = run / "native_check" / "native.log"
    log = log_path.read_text() if log_path.exists() else ""
    proved = r.get("status") == "processed" and r.get("exit_code") == 0 and "val final =" in log
    errors = [l.strip() for l in log.splitlines() if re.search(r"HOL_ERR|Exception|error:|Failed|failed", l)][:8]
    return proved, (run / "native_check" / "kernel_ast.json").exists(), errors


def run_z3(run, where, host):
    cmd = [sys.executable, str(TOOLS / "reply_check" / "z3_engine.py"), str(run), "--host", host]
    if where == "local":
        cmd.append("--local")
    r = subprocess.run(cmd, cwd=WORKBENCH, capture_output=True, text=True)
    (run / "z3_engine.out").write_text(r.stdout + r.stderr)
    path = run / "z3_engine" / "z3_engine.json"
    return json.loads(path.read_text()) if path.exists() else None


def run_english(run):
    r = subprocess.run([sys.executable, str(TOOLS / "reply_check" / "plain_english.py"), str(run), "--no-names"],
                       cwd=WORKBENCH, capture_output=True, text=True)
    path = run / "gloss_claims" / "plain_nonames.txt"
    return path.read_text() if r.returncode == 0 and path.exists() else None


def verdict_of(proved, z):
    v = {"proved": proved}
    if z is None:
        v.update(consistent=None, minimal=None, idle_premises=[], idle_axioms=[], hard_flaws={})
    else:
        concs = z["conclusions"]
        needed = {s: any(c["supports"] and all(s in sup for sup in c["supports"]) for c in concs) for s in z["starts"]}
        v.update(consistent=z["consistent"] == "consistent",
                 inconsistency_confirmed_by_hol4=z.get("contradiction_confirmed_by_hol4"),
                 premises=list(z["starts"]),
                 idle_premises=[s for s, ok in needed.items() if not ok],
                 lists_complete=all(c.get("complete") for c in concs),
                 idle_axioms=list(z["isolated"]),
                 hard_flaws={k: z[k] for k in FLAWS if z.get(k)})
        v["minimal"] = not v["idle_premises"] and v["lists_complete"]
    v["argument"] = bool(proved and v["consistent"] and v["minimal"] and not v["idle_axioms"] and not v["hard_flaws"])
    return v


def report(name, v, errors, english, z3_text):
    yes = lambda b: "yes" if b else ("not checked" if b is None else "no")
    lines = [f"# {name}", "",
             f"**Verdict: {'an argument (consistent, proves its claim, minimal)' if v['argument'] else 'not an argument as it stands'}**", "",
             f"- Proved by HOL4: {yes(v['proved'])}",
             f"- Premises consistent: {yes(v['consistent'])}",
             f"- Every premise needed (minimal): {yes(v['minimal'])}",
             f"- No idle axiom: {yes(v['consistent'] is not None and not v['idle_axioms'])}",
             f"- No hard flaw: {yes(v['consistent'] is not None and not v['hard_flaws'])}", ""]
    if errors and not v["proved"]:
        lines += ["## HOL4 errors", "", *[f"    {e}" for e in errors], ""]
    if v.get("idle_premises"):
        lines += ["## Premises the conclusion does not need", "", *[f"- {p}" for p in v["idle_premises"]], ""]
    if v.get("idle_axioms"):
        lines += ["## Axioms cut off from the conclusion", "", *[f"- {p}" for p in v["idle_axioms"]], ""]
    if v.get("hard_flaws"):
        lines += ["## Hard flaws", "", "```", json.dumps(v["hard_flaws"], indent=1), "```", ""]
    if english:
        lines += ["## The argument in plain English", "", english.strip(), ""]
    if z3_text:
        lines += ["## Z3 engine report", "", "```", z3_text.strip(), "```", ""]
    return "\n".join(lines)


def verify(src, out_root, host, z3_where, theorem, timeout, english=True):
    src = Path(src).resolve()
    run = Path(out_root).resolve() / src.stem
    if run.exists():
        shutil.rmtree(run)
    run.mkdir(parents=True)
    (run / "source.sml").write_text(with_final(src.read_text(), theorem))
    proved, exported, errors = run_hol4(run, host, timeout)
    z = run_z3(run, z3_where, host) if proved and exported else None
    v = verdict_of(proved, z)
    eng = run_english(run) if english and proved else None
    z3_path = run / "z3_engine" / "z3_engine.txt"
    (run / "verdict.json").write_text(json.dumps(v, indent=1))
    (run / "report.md").write_text(report(src.name, v, errors, eng, z3_path.read_text() if z3_path.exists() else ""))
    return v, run


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("sources", nargs="+", help="HOL4 theory files (.sml)")
    ap.add_argument("--theorem", default="final", help="the theorem that states the conclusion (default: final)")
    ap.add_argument("--out", default="holverify_out", help="folder for the reports (default: holverify_out)")
    ap.add_argument("--host", default=os.environ.get("HOLVERIFY_HOST", "mini"))
    ap.add_argument("--hol4", default=os.environ.get("HOLVERIFY_HOL4"))
    ap.add_argument("--remote-dir", default=os.environ.get("HOLVERIFY_REMOTE_DIR"))
    ap.add_argument("--remote-python", default=os.environ.get("HOLVERIFY_REMOTE_PYTHON"))
    ap.add_argument("--z3", choices=["local", "host"], default=None)
    ap.add_argument("--timeout", type=int, default=600, help="seconds for HOL4 (default: 600)")
    ap.add_argument("--no-english", action="store_true")
    ap.add_argument("--json", action="store_true", help="print the verdicts as JSON")
    a = ap.parse_args()
    for key, val in (("HOLVERIFY_HOL4", a.hol4), ("HOLVERIFY_REMOTE_DIR", a.remote_dir),
                     ("HOLVERIFY_REMOTE_PYTHON", a.remote_python)):
        if val:
            os.environ[key] = val
    z3_where = a.z3
    if z3_where is None:
        try:
            import z3  # noqa: F401
            z3_where = "local"
        except ImportError:
            z3_where = "host"
    results = {}
    for s in a.sources:
        print(f"{s}:")
        v, run = verify(s, a.out, a.host, z3_where, a.theorem, a.timeout, not a.no_english)
        results[s] = v
        if not a.json:
            mark = "ARGUMENT" if v["argument"] else "NOT AN ARGUMENT"
            print(f"  {mark}  proved={v['proved']} consistent={v['consistent']} minimal={v['minimal']} "
                  f"idle_premises={len(v.get('idle_premises', []))} idle_axioms={len(v.get('idle_axioms', []))} "
                  f"hard_flaws={len(v.get('hard_flaws', {}))}  report: {run / 'report.md'}")
    if a.json:
        print(json.dumps(results, indent=1))
    sys.exit(0 if all(v["argument"] for v in results.values()) else 1)


if __name__ == "__main__":
    main()
