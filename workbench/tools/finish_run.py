"""Finish a run whose model call came back but whose runner stopped before fetching the answer (on 2026-10-21 the
runners' parent processes were stopped, and each runner died at its next print on the closed pipe). The answer is on
the mini; this fetches it, records the generation result and runs the HOL4 check, as run_native.py or fix_round.py
would have. No model call.

  python3 tools/finish_run.py runs/DATE/RUN
"""
import argparse, json, subprocess, sys
from pathlib import Path

HOL = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HOL / "tools"))
from native_check import check


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--host", default="mini")
    a = ap.parse_args()
    out = Path(a.run).resolve()
    if (out / "generation_result.json").exists():
        raise SystemExit("already finished")
    if not (out / "call.log").exists():
        raise SystemExit("the call never came back: nothing to finish")
    remote = "thick_training/cloud_gen/" + out.name
    subprocess.run(["scp", "-q", f"{a.host}:{remote}/r1_response.json", f"{a.host}:{remote}/r1_response.raw.json",
                    str(out) + "/"], check=True)
    response = json.loads((out / "r1_response.json").read_text())
    content = response.get("content") or ""
    (out / "response.txt").write_text(content)
    status = ("generation_filtered" if response.get("finish") == "content_filter"
              else "response_received" if content.strip() else "no_response")
    (out / "generation_result.json").write_text(json.dumps(
        {"status": status, "finish": response.get("finish"), "content_characters": len(content),
         "usage": response.get("usage")}, indent=2))
    manifest_path = out / "run_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    fix = "fix_of" in manifest                          # a fix round (fix_round.py) rather than a first call
    if fix:
        manifest["state"] = status
    manifest["finished_by"] = "finish_run.py"
    manifest_path.write_text(json.dumps(manifest, indent=2))
    if status != "response_received":
        print(status); return
    res = check(out / "r1_response.json", out / "native_check", "hol4", a.host, timeout=1200 if fix else 300)
    for name in ("controlled_english.txt", "source_declarations_english.txt"):
        if (out / "native_check" / name).exists() and not (out / ("mechanical_english.txt" if name == "controlled_english.txt" else name)).exists():
            (out / ("mechanical_english.txt" if name == "controlled_english.txt" else name)).symlink_to("native_check/" + name)
    print(json.dumps({k: res.get(k) for k in ("status", "exit_code", "elapsed_seconds")}))


if __name__ == "__main__":
    main()
