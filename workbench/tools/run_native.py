"""One model response, checked by a native HOL tool without a revision loop.

Uses the existing case-system + prompt-file / case-user message construction
and the existing loop_call.py execution route. Never adds instructions or feedback.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

from native_check import check


BASE = Path(__file__).resolve().parent.parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("case")
    ap.add_argument("--out", required=True)
    ap.add_argument("--prompt", default="prompts/numbered/37_interface.txt")
    ap.add_argument("--user-file", help="Use the exact user query in this file instead of the original case query")
    ap.add_argument("--inputs", default="data/ab5_inputs.json", help="the case file (key, system, user), relative to hol/")
    ap.add_argument("--prover", choices=["hol4", "isabelle"], default="hol4")
    ap.add_argument("--theory-name", help="For Isabelle, the unchanged output's theory name")
    ap.add_argument("--host", default="mini")
    ap.add_argument("--model", help="OpenRouter model id; default Opus 5.5 (see loop_call.py)")
    ap.add_argument("--provider", help="comma-separated OpenRouter provider tags for --model, no fallbacks")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--revisions", type=int, choices=[0], default=0,
                    help="Only a single generation is supported; no unapproved feedback prompts")
    ap.add_argument("--parallel", action="store_true", help="Compatibility flag; checks never kill other runs")
    ap.add_argument("--generate-only", action="store_true")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    prompt_path = Path(args.prompt)
    if not prompt_path.is_absolute():
        prompt_path = BASE / prompt_path
    prompt_bytes = prompt_path.read_bytes()
    template = prompt_bytes.decode().strip()
    case = next(c for c in json.loads((BASE / args.inputs).read_text()) if c["key"] == args.case)
    original_user = case["user"]
    user_path = None
    if args.user_file:
        user_path = Path(args.user_file).resolve()
        case = dict(case, user=user_path.read_bytes().decode())
        if not case["user"].strip():
            ap.error("User query file is empty")
        (out / "user_prompt.txt").write_bytes(user_path.read_bytes())
        (out / "original_user.txt").write_text(original_user)
    (out / "case_input.json").write_text(json.dumps(
        {k: case[k] for k in ("key", "system", "user")}, ensure_ascii=False, indent=2))
    (out / "run_native.py").write_bytes(Path(__file__).read_bytes())
    # Identical message construction to the preserved legacy runner.
    messages = [{"role": "system", "content": (case["system"].strip() + "\n\n" + template).strip()},
                {"role": "user", "content": case["user"]}]
    (out / "r1_messages.json").write_text(json.dumps(messages, ensure_ascii=False, indent=1))
    (out / "prompt.txt").write_bytes(prompt_bytes)
    call_source = (BASE / "tools" / "loop_call.py").read_bytes()
    (out / "loop_call.py").write_bytes(call_source)
    if args.model:
        (out / "model.json").write_text(json.dumps({"model": args.model, "provider": (args.provider or "").split(",") if args.provider else []}))
    (out / "run_manifest.json").write_text(json.dumps({
        "case": args.case, "prompt_file": str(prompt_path),
        "prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "call_script_sha256": hashlib.sha256(call_source).hexdigest(),
        "user_file": str(user_path) if user_path else None,
        "user_sha256": hashlib.sha256(case["user"].encode()).hexdigest(),
        "original_user_sha256": hashlib.sha256(original_user.encode()).hexdigest(),
        "input_condition": "User-approved replacement query" if user_path else "Original case query",
        "route": (f"OpenRouter; {args.model} from {args.provider}; " if args.model else "OpenRouter; Anthropic provider; ") + "existing loop_call.py",
        "checker": "native", "prover": args.prover, "revisions": 0,
    }, indent=2))
    # Keep model calls separate from the checker, which itself makes no model calls.
    remote = "thick_training/cloud_gen/" + out.name
    subprocess.run(["ssh", "-o", "BatchMode=yes", args.host, "mkdir -p " + shlex.quote(remote)], check=True)
    subprocess.run(["scp", "-q", str(out / "loop_call.py"), str(out / "r1_messages.json"),
                    *([str(out / "model.json")] if (out / "model.json").exists() else []), f"{args.host}:{remote}/"], check=True)
    remote_call = ("read -r K; cd " + shlex.quote(remote) +
                   ' && OPENROUTER_API_KEY="$K" python3 loop_call.py r1_messages.json r1_response.json')
    # Same credential pipe and model route as the old runner; never prints the key.
    key_process = subprocess.Popen(["zsh", "-ic", 'printf "%s\\n" "$OPENROUTER_API_KEY"'],
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    try:
        call = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", args.host, remote_call],
                              stdin=key_process.stdout, capture_output=True, text=True, timeout=2 * 2400 + 600)
    finally:
        key_process.stdout.close()
        key_process.wait()
    (out / "call.log").write_text(call.stdout + call.stderr)
    call.check_returncode()
    print(call.stdout.strip(), flush=True)
    subprocess.run(["scp", "-q", f"{args.host}:{remote}/r1_response.json",
                    f"{args.host}:{remote}/r1_response.raw.json", str(out) + "/"], check=True)
    response = json.loads((out / "r1_response.json").read_text())
    (out / "response.txt").write_text(response.get("content") or "")
    generation_status = ("generation_filtered" if response.get("finish") == "content_filter" else
                         "no_response" if not (response.get("content") or "").strip() else "response_received")
    generation = {"status": generation_status, "finish": response.get("finish"),
                  "content_characters": len(response.get("content") or ""), "usage": response.get("usage")}
    (out / "generation_result.json").write_text(json.dumps(generation, indent=2))
    print(json.dumps(generation), flush=True)
    if not args.generate_only:
        result = check(out / "r1_response.json", out / "native_check", args.prover, args.host,
                       theory_name=args.theory_name, timeout=args.timeout)
        print(json.dumps(result, indent=2))
        full_english = out / "native_check" / "controlled_english.txt"
        if full_english.exists():
            (out / "mechanical_english.txt").symlink_to("native_check/controlled_english.txt")
            (out / "source_declarations_english.txt").symlink_to("native_check/source_declarations_english.txt")
            print("Mechanical English: " + str(out / "mechanical_english.txt"), flush=True)
    print("Saved in " + str(out), flush=True)
    if generation_status != "response_received" or (not args.generate_only and result["status"] != "processed"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
