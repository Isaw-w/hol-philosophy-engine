"""Round 3, reflective equilibrium: continue the review-round conversation with the generated list of places where the
cited response and the argument do not match (tools/reply_check/equilibrium_message.py), unchanged. The model returns
"no", or a revised argument in one HOL4 code block followed by the revised response; the argument is checked with HOL4.

  python3 tools/equilibrium_round.py runs/DATE/REVIEW_RUN --out runs/DATE/NEW_RUN
  python3 tools/equilibrium_round.py runs/DATE/REVIEW_RUN --message prompts/rounds/drafts/round_3_reflective_equilibrium_v3.txt --out runs/DATE/NEW_RUN
"""
import argparse, hashlib, json, re, shutil
from pathlib import Path

from native_check import check
from round2 import execute_call

BASE = Path(__file__).resolve().parent.parent
digest = lambda b: hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source"); ap.add_argument("--out", required=True)
    ap.add_argument("--message", help="send this file instead of REVIEW_RUN/round3_message/message.txt")
    ap.add_argument("--host", default="mini"); ap.add_argument("--timeout", type=int, default=1200)
    a = ap.parse_args()
    src, out = Path(a.source).resolve(), Path(a.out).resolve()
    message = Path(a.message or src / "round3_message/message.txt").read_text().rstrip("\n")
    raw = json.loads((src / "r1_response.raw.json").read_text())
    messages = json.loads((src / "r1_messages.json").read_text()) + [raw["choices"][0]["message"],
                                                                    {"role": "user", "content": message}]
    out.mkdir(parents=True, exist_ok=False)
    message_bytes = json.dumps(messages, ensure_ascii=False, indent=1).encode()
    (out / "r1_messages.json").write_bytes(message_bytes)
    (out / "equilibrium_message.txt").write_text(message + "\n")
    shutil.copy(BASE / "tools/loop_call.py", out / "loop_call.py")
    shutil.copy(Path(__file__), out / "equilibrium_round.py")
    shutil.copy(src / "case_input.json", out / "case_input.json")
    if (src / "model.json").exists():                  # the same model continues its own conversation
        shutil.copy(src / "model.json", out / "model.json")
    case = json.loads((src / "case_input.json").read_text())
    manifest = {"state": "prepared", "round": 3, "kind": "reflective_equilibrium", "continues": str(src), "case": case["key"],
                "messages_sha256": digest(message_bytes), "message_sha256": digest(message.encode()),
                "route": "Opus 5.5 via OpenRouter -> Anthropic, high reasoning, " + a.host,
                "input_condition": "The review-round conversation, its assistant message with reasoning_details, then the "
                                   "generated mismatch list and the reflective-equilibrium request unchanged."
                                   if not a.message else f"The review-round conversation, its assistant message with "
                                   f"reasoning_details, then {a.message} unchanged."}
    (out / "run_manifest.json").write_text(json.dumps(manifest, indent=2))
    execute_call(out, a.host, manifest)
    content = (out / "response.txt").read_text()
    if content.strip().lower().rstrip(".") == "no":
        print(json.dumps({"branch": "no change"}), flush=True); return
    m = re.search(r"^ {0,3}```[^\n]*\n.*?^ {0,3}```[ \t]*$", content, re.M | re.S)
    if m:
        (out / "revised_response.txt").write_text(content[m.end():].strip() + "\n")
        res = check(out / "r1_response.json", out / "native_check", "hol4", a.host, timeout=a.timeout)
        print(json.dumps({"branch": "revised", **{k: res.get(k) for k in ("status", "exit_code", "elapsed_seconds")}}), flush=True)
    else:
        (out / "revised_response.txt").write_text(content.strip() + "\n")
        print(json.dumps({"branch": "response only"}), flush=True)


if __name__ == "__main__":
    main()
