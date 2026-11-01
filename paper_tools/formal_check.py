"""Check formal arguments (DIR/source.sml) with HOL4 and the workbench's Z3 engine, and print what each check found.

  python3 formal_check.py ESSAY/formal/watson2019/route1 [DIR ...]

Runs HOL4 on the Mac mini (native_check: is `final` proved?), the renderer (mechanical English, names kept), and the
workbench's Z3 engine (tools/reply_check/z3_engine.py, on the mini): consistency, every smallest support of each
conclusion of `final` (follows / does not, with a countermodel checked in HOL semantics / unknown), isolated
starting points, and the hard flaws it detects. A premise is needed when some conclusion has it in every smallest
support (the lists complete); the premises are minimal (Besnard and Hunter) when every one is needed. All directories
run in parallel, at most SLOTS at a time. Old tool output in each DIR is replaced. Nothing here calls a model.
"""
import json, shutil, subprocess, sys, threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HOL = Path("/Users/cy/Desktop/Fun/possibility_calculator/Learn/experiments/moral-reasoning/experiments/data/"
           "thick_training/difficult_advice_v2/cloud_gen/hol")
SLOTS = 9                                   # processes on the mini at once; one core left for the system
OLD = ("hidden_premises", "isolated_parts", "argument_checks")   # the earlier checkers, replaced by the Z3 engine
sys.path.insert(0, str(HOL / "tools"))
from native_check import check              # noqa: E402

slots = threading.Semaphore(SLOTS)


def run_one(d):
    for sub in ("native_check", "gloss_claims", "z3_engine") + OLD:
        if (d / sub).is_dir():
            shutil.rmtree(d / sub)
    for f in [d / f"{t}.out" for t in OLD]:
        f.unlink(missing_ok=True)
    with slots:
        r = check(d / "source.sml", d / "native_check", "hol4", "mini", timeout=600)
    log = (d / "native_check" / "native.log").read_text() if (d / "native_check" / "native.log").exists() else ""
    proved = "val final =" in log
    if not proved:
        return r, log, proved, None
    subprocess.run([sys.executable, "tools/reply_check/plain_english.py", str(d)], cwd=HOL, capture_output=True)
    gloss = d / "gloss_claims" / "plain.txt"
    if gloss.exists():
        (d / "mechanical.txt").write_text(gloss.read_text())
    with slots:
        p = subprocess.run([sys.executable, "tools/reply_check/z3_engine.py", str(d)], cwd=HOL, capture_output=True, text=True)
    (d / "z3_engine.out").write_text(p.stdout + p.stderr)
    j = d / "z3_engine" / "z3_engine.json"
    return r, log, proved, (json.loads(j.read_text()) if j.exists() else None)


def report(d, r, log, proved, z):
    L = [f"=== {d}", f"HOL4: {r.get('status')} exit {r.get('exit_code')}; final proved: {proved}"]
    if not proved:
        return "\n".join(L + [log[-3000:]])
    if z is None:
        return "\n".join(L + ["Z3 engine: no result (see z3_engine.out)"])
    starts, concs = z["starts"], z["conclusions"]
    complete = all(c.get("complete") for c in concs)
    needed = {s: any(c["supports"] and all(s in sup for sup in c["supports"]) for c in concs) for s in starts}
    L.append("conclusions: " + "; ".join(f"{c['j']} {c['follows_from_all']} ({len(c['supports'])} smallest set"
                                         f"{'' if len(c['supports']) == 1 else 's'})" for c in concs)
             + ("" if complete else "; NOT every list complete"))
    L.append("premises: " + ", ".join(f"{s.removeprefix('axiom ')} {'needed' if needed[s] else 'NOT NEEDED'}" for s in starts))
    L.append(f"minimal (every premise needed): {complete and all(needed.values())}")
    L.append("unused axioms: " + str(len(z["isolated"])) + ("" if not z["isolated"] else " " + ", ".join(map(str, z["isolated"]))))
    L.append("consistent: " + str(z["consistent"] == "consistent") + ("" if z["consistent"] in ("consistent", "inconsistent") else f" ({z['consistent']})"))
    flaws = {k: z.get(k) for k in ("takes_truth_value", "text_contents", "creative", "collapse", "explosion", "circular")
             if z.get(k)}
    if z.get("final_is_axiom"):
        flaws["final_is_axiom"] = True
    L.append("hard flaws: " + (json.dumps(flaws, ensure_ascii=False) if flaws else "none"))
    cm = z.get("countermodels", {})
    L.append(f"countermodels checked in HOL semantics: {cm.get('validated', 0)} held, {cm.get('not validated', 0)} did not"
             + (f"; limits hit: {z['limits_hit']}" if z.get("limits_hit") else ""))
    return "\n".join(L)


def main(args):
    dirs = [Path(a).resolve() for a in args]
    with ThreadPoolExecutor(max_workers=SLOTS) as ex:
        results = list(ex.map(run_one, dirs))
    print("\n".join(report(d, *res) for d, res in zip(dirs, results)))
    return 0 if all(res[2] for res in results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
