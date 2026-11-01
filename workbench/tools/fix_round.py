"""One fix round after a failed HOL4 check: continue the round-1 conversation with HOL4's own error lines, unchanged,
followed by "Revise it.", then check the returned source with HOL4. No other feedback, no repair of the source.

  python3 tools/fix_round.py runs/ROUND1_RUN --out runs/NEW_RUN
  python3 tools/fix_round.py runs/ROUND1_RUN --out runs/NEW_RUN --message FILE   # a user-approved message, sent as it is

The new run folder has the same files as a round-1 run (case_input.json, r1_messages.json with the whole conversation,
r1_response.json, r1_response.raw.json, native_check/), so round2.py can continue from it.
"""
import argparse, hashlib, json, re, shutil
from pathlib import Path

from native_check import check
from round2 import execute_call

BASE = Path(__file__).resolve().parent.parent
digest = lambda b: hashlib.sha256(b).hexdigest()
MAX_FIX_ROUNDS = 3          # the user, 2026-10-20: "那就加个上限，最多三轮" (HOL4 errors and checked flaws together)


def fix_rounds_before(src):
    """how many fix rounds led to src, following each run's fix_of back to the round-1 run"""
    n, seen = 0, set()
    while src not in seen:
        seen.add(src)
        m = src / "run_manifest.json"
        fix_of = json.loads(m.read_text()).get("fix_of") if m.exists() else None
        if not fix_of:
            return n
        n += 1
        src = Path(fix_of)
    return n


def hol4_error(log):
    """HOL4's error report as printed: from the last 'on line N' position (or the failure line) to the end"""
    lines = log.rstrip("\n").split("\n")
    fail = max((i for i, l in enumerate(lines) if l.startswith("Native HOL4 execution failed")), default=None)
    if fail is None:
        return None
    # the whole last report: from its "Exception raised" line when there is one, else from the last position line
    # a static (compile-time) error: from the first "source.sml:N: error:" line
    static = [i for i, l in enumerate(lines[:fail]) if re.search(r"source\.sml:\d+: error:", l)]
    if static:
        first = lines[static[0]]
        lines[static[0]] = first[first.index("source.sml:"):]
        return "\n".join(lines[static[0]:fail + 1]).strip()
    raised = [i for i, l in enumerate(lines[:fail]) if l.startswith("Exception raised")]
    start = raised[-1] if raised else max((i for i, l in enumerate(lines[:fail]) if re.match(r"^on line \d+", l)
                                           or "Failed to prove theorem" in l), default=None)
    if start is None:
        # no position in the report: from the last binding HOL4 accepted, which shows where it stopped
        start = max((i for i, l in enumerate(lines[:fail]) if l.startswith("val ")), default=fail)
    return "\n".join(lines[start:fail + 1]).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source"); ap.add_argument("--out", required=True)
    ap.add_argument("--host", default="mini"); ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--message", help="send this file's text as it is (a user-approved message), e.g. a checked flaw")
    ap.add_argument("--extra-rounds", type=int, default=0,
                    help="rounds beyond the limit, only when the user gives them (2026-10-20, GLM on fu178: '再给他三轮')")
    a = ap.parse_args()
    src, out = Path(a.source).resolve(), Path(a.out).resolve()
    done = fix_rounds_before(src)
    if done >= MAX_FIX_ROUNDS + a.extra_rounds:
        raise SystemExit(f"{src.name} already had {done} fix rounds; the limit is {MAX_FIX_ROUNDS + a.extra_rounds}")
    result_file = src / "native_check/native_result.json"
    if a.message:
        error = None
    elif not result_file.exists():
        # HOL4 never ran: the code block could not be taken from the response; send the extractor's own message
        from native_check import source_of
        try:
            source_of((src / "response.txt").read_text())
            raise SystemExit("No HOL4 result and the code block extracts fine")
        except ValueError as exc:
            error = str(exc)
    else:
        result = json.loads(result_file.read_text())
        if result.get("status") == "unproven_theorems":
            error = "Theorems without a proof: " + ", ".join(result.get("unproven_theorems", []))
        elif result.get("status") != "execution_failed":
            raise SystemExit("Source run did not fail its HOL4 check")
        else:
            error = hol4_error((src / "native_check/native.log").read_text())
    if a.message:
        feedback = Path(a.message).read_text().strip()
    elif not error:
        raise SystemExit("No HOL4 error report found in the log")
    else:
        feedback = error + "\n\nRevise it."
    raw = json.loads((src / "r1_response.raw.json").read_text())
    assistant = raw["choices"][0]["message"]
    messages = json.loads((src / "r1_messages.json").read_text()) + [assistant, {"role": "user", "content": feedback}]
    out.mkdir(parents=True, exist_ok=False)
    message_bytes = json.dumps(messages, ensure_ascii=False, indent=1).encode()
    (out / "r1_messages.json").write_bytes(message_bytes)
    (out / "feedback.txt").write_text(feedback)
    shutil.copy(BASE / "tools/loop_call.py", out / "loop_call.py")
    if (src / "model.json").exists():                  # the same model continues its own conversation
        shutil.copy(src / "model.json", out / "model.json")
    shutil.copy(Path(__file__), out / "fix_round.py")
    case = json.loads((src / "case_input.json").read_text())
    shutil.copy(src / "case_input.json", out / "case_input.json")
    src_manifest = json.loads((src / "run_manifest.json").read_text())
    manifest = {"state": "prepared", "round": 1, "fix_of": str(src), "case": case["key"],
                "user_sha256": src_manifest.get("user_sha256", digest(case["user"].encode())),
                "messages_sha256": digest(message_bytes), "feedback": feedback,
                "route": (json.loads((src / "model.json").read_text())["model"] if (src / "model.json").exists()
                          else "Opus 5.5 via OpenRouter -> Anthropic") + ", high reasoning, " + a.host,
                "input_condition": ("Round-1 conversation, the assistant message with reasoning_details, then the user-approved message in "
                                    + a.message) if a.message else
                                   "Round-1 conversation, the failed assistant message with reasoning_details, then HOL4's error lines (or the extractor's message) unchanged and 'Revise it.'"}
    (out / "run_manifest.json").write_text(json.dumps(manifest, indent=2))
    execute_call(out, a.host, manifest)
    res = check(out / "r1_response.json", out / "native_check", "hol4", a.host, timeout=a.timeout)
    print(json.dumps({k: res.get(k) for k in ("status", "exit_code", "elapsed_seconds")}), flush=True)
    for name in ("controlled_english.txt", "source_declarations_english.txt"):
        if (out / "native_check" / name).exists():
            (out / ("mechanical_english.txt" if name == "controlled_english.txt" else name)).symlink_to("native_check/" + name)


if __name__ == "__main__":
    main()
