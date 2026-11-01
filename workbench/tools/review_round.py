"""Round 2 as a review: continue the round-1 conversation with the checked hidden premises and isolated parts
(tools/reply_check/review_message.py), unchanged, and let the model either keep the argument and write the reply, or
revise the argument. A returned HOL4 code block is checked with HOL4; otherwise the reply is saved as it is.

  python3 tools/review_round.py runs/DATE/ROUND1_RUN --out runs/DATE/NEW_RUN
  python3 tools/review_round.py runs/DATE/ROUND1_RUN --message prompts/rounds/drafts/round_2_convert_cite_v2.txt --out runs/DATE/NEW_RUN

The new folder has r1_messages.json (the whole conversation), r1_response.json and .raw.json, response.txt, and either
reply.txt (argument kept) or native_check/ (argument revised).
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
    ap.add_argument("--message", help="send this file instead of ROUND1_RUN/round2_message/message.txt")
    ap.add_argument("--host", default="mini"); ap.add_argument("--timeout", type=int, default=1200)
    a = ap.parse_args()
    src, out = Path(a.source).resolve(), Path(a.out).resolve()
    message = Path(a.message or src / "round2_message/message.txt").read_text().rstrip("\n")
    raw = json.loads((src / "r1_response.raw.json").read_text())
    assistant = raw["choices"][0]["message"]
    messages = json.loads((src / "r1_messages.json").read_text()) + [assistant, {"role": "user", "content": message}]
    out.mkdir(parents=True, exist_ok=False)
    message_bytes = json.dumps(messages, ensure_ascii=False, indent=1).encode()
    (out / "r1_messages.json").write_bytes(message_bytes)
    (out / "review_message.txt").write_text(message + "\n")
    shutil.copy(BASE / "tools/loop_call.py", out / "loop_call.py")
    shutil.copy(Path(__file__), out / "review_round.py")
    shutil.copy(src / "case_input.json", out / "case_input.json")
    if (src / "model.json").exists():                  # the same model continues its own conversation
        shutil.copy(src / "model.json", out / "model.json")
    case = json.loads((src / "case_input.json").read_text())
    manifest = {"state": "prepared", "round": 2, "kind": "review", "review_of": str(src), "case": case["key"],
                "messages_sha256": digest(message_bytes), "message_sha256": digest(message.encode()),
                "route": "Opus 5.5 via OpenRouter -> Anthropic, high reasoning, " + a.host,
                "input_condition": "Round-1 conversation, the round-1 assistant message with reasoning_details, then the "
                                   "generated review message (hidden premises and isolated parts, checked with HOL4) unchanged."
                                   if not a.message else f"Round-1 conversation, the round-1 assistant message with "
                                   f"reasoning_details, then {a.message} unchanged."}
    (out / "run_manifest.json").write_text(json.dumps(manifest, indent=2))
    execute_call(out, a.host, manifest)
    content = (out / "response.txt").read_text()
    if re.search(r"^ {0,3}```", content, re.M):
        res = check(out / "r1_response.json", out / "native_check", "hol4", a.host, timeout=a.timeout)
        print(json.dumps({"branch": "revised", **{k: res.get(k) for k in ("status", "exit_code", "elapsed_seconds")}}), flush=True)
    else:
        (out / "reply.txt").write_text(content)
        print(json.dumps({"branch": "kept", "reply_characters": len(content)}), flush=True)


if __name__ == "__main__":
    main()
