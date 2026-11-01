"""Round 1 for several cases with one model: the call, up to MAX fix rounds after a HOL4 failure (HOL4's own error
lines + "Revise it.", via fix_round.py), then the Z3 checks on the last processed argument. One JSON line per case
is appended to OUT_DIR/summary_<tag>.jsonl. Run only after the user has approved the exact inputs.

  python3 tools/batch_round1.py --inputs data/sample10_20261020/inputs.json --out-dir runs/20261020/sample10_v23 \
      --tag glm53 --model z-ai/glm-5.3 --provider z-ai/fp8
"""
import argparse, json, re, subprocess, sys, time
from pathlib import Path

HOL = Path(__file__).resolve().parent.parent


def status(run):
    gen = json.loads((run / "generation_result.json").read_text()) if (run / "generation_result.json").exists() else {}
    nat = run / "native_check/native_result.json"
    native = json.loads(nat.read_text()).get("status") if nat.exists() else None
    cost = (gen.get("usage") or {}).get("cost")
    return gen.get("status"), native, cost


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", required=True); ap.add_argument("--out-dir", required=True); ap.add_argument("--tag", required=True)
    ap.add_argument("--model"); ap.add_argument("--provider")
    ap.add_argument("--prompt", default="prompts/current/round_1.txt"); ap.add_argument("--max-fix", type=int, default=3)
    ap.add_argument("--cases", nargs="*", help="keys to run (default: all in the inputs file)")
    ap.add_argument("--z3-local", action="store_true", help="run the Z3 checks here rather than on the mini")
    a = ap.parse_args()
    out_dir = HOL / a.out_dir; out_dir.mkdir(parents=True, exist_ok=True)
    keys = a.cases or [c["key"] for c in json.loads((HOL / a.inputs).read_text())]
    m = re.search(r"_(v\d+)", (HOL / a.prompt).resolve().name)     # the prompt's version, e.g. v24
    ver = m.group(1) if m else "vX"
    summary = out_dir / f"summary_{a.tag}.jsonl"
    done = {json.loads(l)["case"] for l in summary.read_text().splitlines() if l.strip()} if summary.exists() else set()
    for key in keys:
        if key in done:                                 # already finished in this folder
            continue
        slug = key.replace("/", "_")
        # resume: a case already started here (by a stopped batch) goes on from its last run
        chain = sorted((r for r in out_dir.glob(f"{slug}_round1_*{ver}_{a.tag}_*") if r.is_dir()), key=lambda r: r.name[-15:])
        if not chain:
            ts = time.strftime("%Y%m%d_%H%M%S")
            run = out_dir / f"{slug}_round1_{ver}_{a.tag}_{ts}"
            cmd = [sys.executable, "tools/run_native.py", key, "--inputs", a.inputs, "--prompt", a.prompt, "--out", str(run)]
            if a.model:
                cmd += ["--model", a.model, "--provider", a.provider]
            subprocess.run(cmd, cwd=HOL, capture_output=True, text=True)
            chain = [run]
        if not (chain[-1] / "generation_result.json").exists() and (chain[-1] / "call.log").exists():
            subprocess.run([sys.executable, "tools/finish_run.py", str(chain[-1])], cwd=HOL, capture_output=True, text=True)
        gen, native, cost = status(chain[-1])
        if gen is None:                                 # the call never came back: leave the case for a rerun
            print(json.dumps({"case": key, "model": a.tag, "interrupted": str(chain[-1].relative_to(HOL))}), flush=True)
            continue
        costs = [status(r)[2] for r in chain]
        n = len(chain) - 1
        while gen == "response_received" and native != "processed" and n < a.max_fix:
            n += 1
            nxt = out_dir / f"{slug}_round1_fix{n}_{ver}_{a.tag}_{time.strftime('%Y%m%d_%H%M%S')}"
            subprocess.run([sys.executable, "tools/fix_round.py", str(chain[-1]), "--out", str(nxt)],
                           cwd=HOL, capture_output=True, text=True)
            if not nxt.exists():
                break
            chain.append(nxt)
            gen, native, cost = status(nxt)
            costs.append(cost)
        z3 = None
        if native == "processed" and (chain[-1] / "native_check/kernel_ast.json").exists():
            subprocess.run([sys.executable, "tools/reply_check/z3_engine.py", str(chain[-1]), "--budget-s", "600"]
                           + (["--local"] if a.z3_local else []), cwd=HOL, capture_output=True, text=True)
            zf = chain[-1] / "z3_engine/z3_engine.json"
            z3 = str(zf.relative_to(HOL)) if zf.exists() else None
        rec = {"case": key, "model": a.tag, "runs": [str(r.relative_to(HOL)) for r in chain], "generation": gen,
               "native": native, "fix_rounds": n, "cost": round(sum(c for c in costs if c), 4), "z3": z3}
        with open(summary, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
