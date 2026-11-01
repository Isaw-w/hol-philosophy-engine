"""Continue round 2 with the round-3 template and round-1 mechanical English.

As in the earlier round 3, preserve the provider's full assistant message,
including reasoning_details. No analyst feedback or earlier round-3 answer is
added. The declared template slot is filled verbatim and both versions saved.
A model call requires --run; returned HOL4 is checked without repairs. A literal
no records a decision not to revise and skips HOL4 execution.
"""
import argparse
import json
from pathlib import Path

from native_check import check
from round2 import BASE, digest, execute_call


def record_no_revision(out, content):
    """Recognize only the prompt's exact sentinel, allowing surrounding whitespace."""
    if content.strip() not in ("no", "Nothing needs to be added."):
        return False
    result = {"status": "no_revision_declared", "prover_called": False,
              "scope": "Model reports no revision needed; this is not a new proof or a fidelity check."}
    (out / "review_result.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return True


def record_unclear(out, content):
    if not content.strip().startswith("Coverage remains unclear:"):
        return False
    result = {"status": "coverage_unresolved", "prover_called": False,
              "explanation": content.strip(),
              "scope": "Model reports unresolved coverage; no completeness or proof claim."}
    (out / "review_result.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return True


def save_prose(out, content):
    """Keep the text around the code block unchanged: after it, a revised response (reflective-equilibrium prompt)."""
    import re
    m = re.search(r"```[^\n]*\n.*?\n```", content, re.S)
    if not m:
        return
    before, after = content[:m.start()].strip(), content[m.end():].strip()
    if before:
        (out / "text_before_code.txt").write_text(before + "\n")
    if after:
        (out / "revised_response.txt").write_text(after + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="A completed round-2 run directory")
    parser.add_argument("--prompt", default="prompts/rounds/round_3_review_logic.txt")
    parser.add_argument("--out", required=True)
    parser.add_argument("--host", default="mini")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--operator-scan", help="JSON review aid with text and source_response_sha256; requires a declared template slot")
    parser.add_argument("--run", action="store_true", help="Make one model call, then check returned HOL4")
    parser.add_argument("--english", choices=["full", "source"], default="full",
                        help="full: mechanical_english.txt (every theorem, including those HOL4 generates for datatypes); "
                             "source: source_declarations_english.txt (only what the source itself declares)")
    args = parser.parse_args()
    source = Path(args.source).resolve()
    out = Path(args.out).resolve()
    prompt = Path(args.prompt)
    if not prompt.is_absolute():
        prompt = BASE / prompt
    prompt_bytes = prompt.read_bytes()
    source_manifest = json.loads((source / "run_manifest.json").read_text())
    message_bytes = (source / "r1_messages.json").read_bytes()
    messages = json.loads(message_bytes)
    raw_bytes = (source / "r1_response.raw.json").read_bytes()
    raw = json.loads(raw_bytes)
    choice = raw["choices"][0]
    assistant = choice["message"]
    normalized = json.loads((source / "r1_response.json").read_text())
    if (source_manifest.get("round") != 2
            or digest(message_bytes) != source_manifest["messages_sha256"]
            or not assistant.get("content", "").strip()
            or assistant.get("role") != "assistant"
            or choice.get("finish_reason") != "stop"
            or assistant["content"] != normalized.get("content")):
        parser.error("Source must be a complete round-2 response with unchanged saved messages")
    template = prompt_bytes.decode()
    marker = "{round_1_mechanical_english}"
    if template.count(marker) != 1:
        parser.error("Round-3 prompt must contain exactly one " + marker + " slot")
    formal_run = Path(source_manifest["source_run"])
    formal_bytes = (formal_run / "r1_response.json").read_bytes()
    if digest(formal_bytes) != source_manifest["source_formal_response_sha256"]:
        parser.error("Round-1 response has changed since round 2")
    english_file = formal_run / ("source_declarations_english.txt" if args.english == "source" else "mechanical_english.txt")
    english_bytes = english_file.read_bytes()
    if not english_bytes.strip():
        parser.error("Round-1 mechanical English is empty")
    resolved_prompt = template.replace(marker, english_bytes.decode())
    scan_marker = "{round_2_operator_scan}"
    scan_path, scan_bytes = None, None
    if args.operator_scan:
        scan_path = Path(args.operator_scan).resolve()
        scan_bytes = scan_path.read_bytes()
        scan = json.loads(scan_bytes)
        if template.count(scan_marker) != 1:
            parser.error("Operator scan requires exactly one " + scan_marker + " slot")
        if scan["source_response_sha256"] != digest(assistant["content"].encode()):
            parser.error("Operator scan was prepared for a different round-2 response")
        if not isinstance(scan.get("text"), str) or not scan["text"].strip():
            parser.error("Operator scan text is empty")
        resolved_prompt = resolved_prompt.replace(scan_marker, scan["text"])
    elif scan_marker in template:
        parser.error("This prompt requires --operator-scan")
    messages += [assistant, {"role": "user", "content": resolved_prompt}]
    next_messages = json.dumps(messages, ensure_ascii=False, indent=1).encode()
    call_source = (BASE / "tools/loop_call.py").read_bytes()
    out.mkdir(parents=True, exist_ok=False)
    (out / "r1_messages.json").write_bytes(next_messages)
    (out / "prompt.txt").write_bytes(prompt_bytes)
    (out / "resolved_prompt.txt").write_text(resolved_prompt)
    (out / "source_mechanical_english.txt").write_bytes(english_bytes)
    if scan_bytes is not None:
        (out / "operator_scan_input.json").write_bytes(scan_bytes)
    (out / "loop_call.py").write_bytes(call_source)
    for filename in ("round3.py", "round2.py", "native_check.py", "native_worker.py",
                     "export_hol4_terms.sml", "verbalize_hol4.py"):
        (out / filename).write_bytes((BASE / "tools" / filename).read_bytes())
    (out / "source_messages.json").write_bytes(message_bytes)
    (out / "source_response.raw.json").write_bytes(raw_bytes)
    (out / "source_run_manifest.json").write_bytes((source / "run_manifest.json").read_bytes())
    manifest = {"state": "prepared", "round": 3, "case": source_manifest["case"],
                "source_run": str(source), "prompt_file": str(prompt),
                "prompt_sha256": digest(prompt_bytes), "messages_sha256": digest(next_messages),
                "resolved_prompt_sha256": digest(resolved_prompt.encode()),
                "prompt_transformation": "Verbatim replacement of declared mechanical-English and optional operator-scan slots; no other instructions added",
                "operator_scan_file": str(scan_path) if scan_path else None,
                "operator_scan_sha256": digest(scan_bytes) if scan_bytes is not None else None,
                "mechanical_english_file": str(english_file.resolve()),
                "mechanical_english_sha256": digest(english_bytes),
                "source_formal_run": str(formal_run),
                "source_formal_response_sha256": digest(formal_bytes),
                "source_messages_sha256": digest(message_bytes),
                "source_raw_response_sha256": digest(raw_bytes),
                "call_script_sha256": digest(call_source),
                "route": "Opus 5.5 via OpenRouter -> Anthropic, high reasoning, " + args.host,
                "input_condition": "Saved round-2 conversation and full returned assistant message, including reasoning_details, followed by current round-3 template with complete mechanical English from the parent round-1 run and any explicitly supplied operator scan inserted verbatim. No previous round-3 output or analyst feedback.",
                "model_call_requested": args.run, "prover": "hol4"}
    (out / "run_manifest.json").write_text(json.dumps(manifest, indent=2))
    if not args.run:
        print("Prepared without a model call: " + str(out))
        return
    execute_call(out, args.host, manifest)
    content = json.loads((out / "r1_response.json").read_text()).get("content") or ""
    if record_no_revision(out, content):
        return
    save_prose(out, content)
    if record_unclear(out, content):
        raise SystemExit(2)
    result = check(out / "r1_response.json", out / "native_check", "hol4", args.host,
                   timeout=args.timeout)
    print(json.dumps(result, indent=2), flush=True)
    if (out / "native_check/controlled_english.txt").exists():
        (out / "mechanical_english.txt").symlink_to("native_check/controlled_english.txt")
        (out / "source_declarations_english.txt").symlink_to("native_check/source_declarations_english.txt")
    if result["status"] != "processed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
