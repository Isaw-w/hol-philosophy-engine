"""Prepare or run natural-language recovery using the earlier round-2 input format.

The prompt file is used unchanged. No mechanical translation, prior prose answer,
hidden reasoning, or analyst corrections are supplied. A model call requires --run.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess


BASE = Path(__file__).resolve().parent.parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="The checked round-1 run directory")
    parser.add_argument("--prompt", default="prompts/rounds/round_2_natural_response.txt")
    parser.add_argument("--out", required=True, help="A new output directory")
    parser.add_argument("--host", default="mini")
    parser.add_argument("--run", action="store_true", help="Make one model call via the existing route")
    parser.add_argument("--continue-round1", action="store_true",
                        help="Continue the round-1 conversation (its system and user messages and the full round-1 assistant "
                             "message, reasoning included), then the round-2 prompt, instead of a fresh conversation")
    args = parser.parse_args()
    source = Path(args.source).resolve()
    out = Path(args.out).resolve()
    prompt = Path(args.prompt)
    if not prompt.is_absolute():
        prompt = BASE / prompt
    prompt_bytes = prompt.read_bytes()
    source_manifest = json.loads((source / "run_manifest.json").read_text())
    case_snapshot = source / "case_input.json"
    if case_snapshot.exists():
        case = json.loads(case_snapshot.read_text())
        if (case["key"] != source_manifest["case"]
                or digest(case["user"].encode()) != source_manifest["user_sha256"]):
            parser.error("Round-1 case snapshot does not match its manifest")
    else:
        case = next(c for c in json.loads((BASE / "data/ab5_inputs.json").read_text())
                    if c["key"] == source_manifest["case"])
    response_bytes = (source / "r1_response.json").read_bytes()
    formal = json.loads(response_bytes).get("content") or ""
    check_bytes = (source / "native_check/native_result.json").read_bytes()
    checked = json.loads(check_bytes)
    check_manifest = json.loads((source / "native_check/manifest.json").read_text())
    if (not formal.strip() or checked.get("status") != "processed"
            or checked.get("prover") != "hol4"
            or check_manifest["original_sha256"] != digest(response_bytes)):
        parser.error("Source must contain the unchanged response accepted by its HOL4 check")
    # Same headings, placement, and case system as the preserved earlier round 2.
    user = ("Original user query:\n" + case["user"]
            + "\n\nChecked HOL4 argument:\n" + formal
            + "\n\nHOL4 result:\n" + json.dumps(checked, ensure_ascii=False, indent=2)
            + "\n\n" + prompt_bytes.decode())
    messages = [{"role": "system", "content": case["system"]},
                {"role": "user", "content": user}]
    if args.continue_round1:
        raw = json.loads((source / "r1_response.raw.json").read_text())
        assistant = raw["choices"][0]["message"]
        if assistant.get("role") != "assistant" or assistant.get("content") != formal:
            parser.error("Round-1 raw message does not match its saved response")
        messages = json.loads((source / "r1_messages.json").read_text()) + [
            assistant, {"role": "user", "content": prompt_bytes.decode()}]
    message_bytes = json.dumps(messages, ensure_ascii=False, indent=1).encode()
    call_source = (BASE / "tools/loop_call.py").read_bytes()
    out.mkdir(parents=True, exist_ok=False)
    (out / "r1_messages.json").write_bytes(message_bytes)
    (out / "prompt.txt").write_bytes(prompt_bytes)
    (out / "loop_call.py").write_bytes(call_source)
    (out / "round2.py").write_bytes(Path(__file__).read_bytes())
    (out / "source_response.json").write_bytes(response_bytes)
    (out / "source_native_result.json").write_bytes(check_bytes)
    (out / "source_check_manifest.json").write_bytes((source / "native_check/manifest.json").read_bytes())
    manifest = {"state": "prepared", "round": 2, "case": case["key"],
                "source_run": str(source), "prompt_file": str(prompt),
                "prompt_sha256": digest(prompt_bytes), "messages_sha256": digest(message_bytes),
                "source_formal_response_sha256": digest(response_bytes),
                "source_verification_sha256": digest(check_bytes),
                "call_script_sha256": digest(call_source),
                "route": "Opus 5.5 via OpenRouter -> Anthropic, high reasoning, " + args.host,
                "input_condition": ("Continuation of the round-1 conversation: its system and user messages, the full round-1 assistant message including reasoning_details, then the current round-2 prompt unchanged."
                                    if args.continue_round1 else
                                    "Original case system and query, checked public formal argument and native result, current round-2 prompt; no prior prose, hidden reasoning, mechanical translation, or analyst corrections."),
                "conversation": "continued from round 1" if args.continue_round1 else "fresh",
                "output_kind": "natural-language reconstruction; not a HOL4 verification",
                "model_call_requested": args.run}
    manifest_path = out / "run_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2))
    if not args.run:
        print("Prepared without a model call: " + str(out))
        return
    execute_call(out, args.host, manifest)


def execute_call(out, host, manifest):
    """Execute the saved messages using the existing provider and credential pipe."""
    manifest_path = out / "run_manifest.json"
    remote = "thick_training/cloud_gen/" + out.name
    subprocess.run(["ssh", "-o", "BatchMode=yes", host,
                    "mkdir " + shlex.quote(remote)], check=True)
    subprocess.run(["scp", "-q", str(out / "loop_call.py"), str(out / "r1_messages.json"),
                    *([str(out / "model.json")] if (out / "model.json").exists() else []), f"{host}:{remote}/"], check=True)
    remote_call = ("read -r K; cd " + shlex.quote(remote)
                   + ' && OPENROUTER_API_KEY="$K" python3 loop_call.py r1_messages.json r1_response.json')
    key_process = subprocess.Popen(["zsh", "-ic", 'printf "%s\\n" "$OPENROUTER_API_KEY"'],
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    try:
        call = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", host, remote_call],
                              stdin=key_process.stdout, capture_output=True, text=True, timeout=2 * 2400 + 600)
    finally:
        key_process.stdout.close()
        key_process.wait()
    (out / "call.log").write_text(call.stdout + call.stderr)
    call.check_returncode()
    print(call.stdout.strip(), flush=True)
    subprocess.run(["scp", "-q", f"{host}:{remote}/r1_response.json",
                    f"{host}:{remote}/r1_response.raw.json", str(out) + "/"], check=True)
    response = json.loads((out / "r1_response.json").read_text())
    content = response.get("content") or ""
    (out / "response.txt").write_text(content)
    status = ("generation_filtered" if response.get("finish") == "content_filter"
              else "response_received" if content.strip() else "no_response")
    generation = {"status": status, "finish": response.get("finish"),
                  "content_characters": len(content), "usage": response.get("usage")}
    (out / "generation_result.json").write_text(json.dumps(generation, indent=2))
    manifest["state"] = status
    manifest_path.write_text(json.dumps(manifest, indent=2))
    print("Saved in " + str(out), flush=True)
    if status != "response_received":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
