"""Check saved output with HOL4 or Isabelle's own frontend, without rewriting it.

  python3 tools/native_check.py response.json --prover hol4 --out checks/fresh-name
  python3 tools/native_check.py MyTheory.thy --prover isabelle --out checks/fresh-name
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import uuid


def source_of(text, block=None):
    """Select a Markdown code container, not a logical expression or proof."""
    lines = text.splitlines(keepends=True)
    blocks, inside, start, opening = [], False, 0, None
    fence = None
    for i, line in enumerate(lines):
        body = line.rstrip("\r\n")
        match = re.fullmatch(r" {0,3}(`{3,}|~{3,})([^\r\n]*)", body) if not inside else None
        if match and not (match[1][0] == "`" and "`" in match[2]):
            inside, start, opening, fence = True, i + 1, i, match[1]
        elif inside and re.fullmatch(r" {0,3}" + re.escape(fence[0]) + "{" + str(len(fence)) + r",}[ \t]*", body):
            blocks.append(("".join(lines[start:i]), opening + 1, i + 1))
            inside = False
    if inside:
        raise ValueError("Unclosed code fence; source was not repaired")
    if not blocks:
        if block is not None:
            raise ValueError("No fenced code block to select")
        return text, {"kind": "identity"}
    if len(blocks) != 1 and block is None:
        raise ValueError("Multiple code blocks: select one explicitly with --block (1-based)")
    index = 0 if block is None else block - 1
    if index < 0 or index >= len(blocks):
        raise ValueError("Code block index is out of range")
    code, first, last = blocks[index]
    return code, {"kind": "markdown_container_extraction", "block": index + 1,
                  "opening_line": first, "closing_line": last, "block_count": len(blocks),
                  "note": "Only the selected container's contents are executed. The complete response is preserved."}


def check(source, out, prover, host="mini", block=None, theory_name=None, timeout=300):
    source, out = Path(source).resolve(), Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    raw = source.read_bytes()
    (out / "original").mkdir()
    (out / "original" / source.name).write_bytes(raw)
    def not_checked(status, reason, finish=None):
        result = {"status": status, "reason": reason, "model_finish": finish,
                  "prover": prover, "checker_executed": False, "model_calls": 0,
                  "scope": "No proof checking was performed; this is not a verified response."}
        (out / "manifest.json").write_text(json.dumps({
            "created_utc": datetime.now(timezone.utc).isoformat(), "original_file": str(source),
            "original_sha256": hashlib.sha256(raw).hexdigest(), "prover": prover,
            "checker_executed": False, "model_calls": 0}, indent=2))
        (out / "native_result.json").write_text(json.dumps(result, indent=2))
        return result
    text = raw.decode("utf-8")
    record = {}
    if source.suffix == ".json":
        record = json.loads(text)
        text = next((record[key] for key in ("content", "representation", "answer")
                     if isinstance(record.get(key), str)), None)
        if text is None:
            raise ValueError("No string content, representation, or answer in response")
    (out / "response.txt").write_text(text)
    if record.get("finish") == "content_filter":
        return not_checked("generation_filtered", "Provider reported content_filter; original response preserved.", "content_filter")
    if not text.strip():
        return not_checked("no_response", "The response contains no text.", record.get("finish"))
    if source.suffix.lower() in (".thy", ".sml", ".ml"):
        if block is not None:
            raise ValueError("Native source files execute unchanged; --block applies to response containers")
        code, transformation = text, {"kind": "native_source_identity"}
    else:
        code, transformation = source_of(text, block)
    if not code.strip():
        return not_checked("no_formal_source", "The selected code block is empty.", record.get("finish"))
    if prover == "isabelle":
        # Filename is an explicit execution parameter, never inferred by parsing HOL.
        name = theory_name or (source.stem if source.suffix == ".thy" else None)
        if not name or not name.isidentifier():
            raise ValueError("For Isabelle JSON output, supply --theory-name matching its unchanged theory header")
        filename = name + ".thy"
    else:
        filename = "source.sml"
    (out / filename).write_text(code)
    worker = Path(__file__).with_name("native_worker.py")
    (out / worker.name).write_bytes(worker.read_bytes())
    uploads = [str(out / filename), str(out / worker.name)]
    if prover == "hol4":
        exporter = Path(__file__).with_name("export_hol4_terms.sml")
        (out / exporter.name).write_bytes(exporter.read_bytes())
        uploads.append(str(out / exporter.name))
    local = host == "local"                             # running on the mini itself (mini_scheduler.py): no ssh
    remote = str(out) if local else "thick_training/native_hol_checks/" + uuid.uuid4().hex
    manifest = {"created_utc": datetime.now(timezone.utc).isoformat(), "original_file": str(source),
                "original_sha256": hashlib.sha256(raw).hexdigest(),
                "executed_source_sha256": hashlib.sha256(code.encode()).hexdigest(),
                "transformation": transformation, "prover": prover, "host": host,
                "remote_directory": remote, "timeout_seconds": timeout,
                "added_domain_operators": [], "rewritten_formulas": False,
                "replaced_proofs": False, "model_calls": 0}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if local:                                           # the worker runs in out itself and writes its results there
        import sys
        command = [sys.executable, "native_worker.py", "--prover", prover, "--timeout", str(timeout)] + \
                  (["--export-ast"] if prover == "hol4" else [])
        run = subprocess.run(command, cwd=out, capture_output=True, text=True, timeout=timeout + 600)
    else:
        subprocess.run(["ssh", "-o", "BatchMode=yes", host, "mkdir -p " + shlex.quote(remote)], check=True)
        subprocess.run(["scp", "-q", *uploads, f"{host}:{remote}/"], check=True)
        command = "cd " + shlex.quote(remote) + " && python3 native_worker.py --prover " + prover + " --timeout " + str(timeout)
        if prover == "hol4":
            command += " --export-ast"
        run = subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ServerAliveInterval=30", host, command],
                             capture_output=True, text=True, timeout=timeout + 600)
    (out / "transport.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError("Native worker failed; see transport.log")
    if not local:
        for name in ("native_result.json", "native.log"):
            subprocess.run(["scp", "-q", f"{host}:{remote}/{name}", str(out / name)], check=True)
    result = json.loads((out / "native_result.json").read_text())
    if prover == "hol4":
        # Preserve the exact session driver used to load and inspect the source.
        if not local:
            subprocess.run(["scp", "-q", f"{host}:{remote}/driver.sml", str(out / "driver.sml")], check=True)
        if result["status"] == "processed" and result.get("ast_export_status") == "exported":
            if not local:
                subprocess.run(["scp", "-q", f"{host}:{remote}/kernel_ast.json", str(out / "kernel_ast.json")], check=True)
            try:
                from verbalize_hol4 import write_outputs
                write_outputs(out / "kernel_ast.json", out)
            except Exception as exc:
                # A presentation failure must not change a native proof's result.
                (out / "verbalization_result.json").write_text(json.dumps({
                    "status": "rendering_failed", "error": str(exc), "model_calls": 0}, indent=2))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source")
    ap.add_argument("--out", required=True)
    ap.add_argument("--prover", choices=["hol4", "isabelle"], required=True)
    ap.add_argument("--host", default="mini")
    ap.add_argument("--block", type=int)
    ap.add_argument("--theory-name")
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()
    result = check(args.source, args.out, args.prover, args.host, args.block, args.theory_name, args.timeout)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["status"] == "processed" else 1)


if __name__ == "__main__":
    main()
