"""Execute source with a native HOL tool. No formula parsing or proof rewriting."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


HOL4_DRIVER = r'''
val _ =
  ((use "source.sml";
    let
      fun jsonString s = "\"" ^ String.translate
        (fn #"\"" => "\\\"" | #"\\" => "\\\\" | #"\n" => "\\n"
          | #"\r" => "\\r" | #"\t" => "\\t" | c => str c) s ^ "\"";
      fun arr f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
      fun entry (name, th) =
        let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
        in "{\"name\":" ^ jsonString name ^
           ",\"statement\":" ^ jsonString (Parse.thm_to_string th) ^
           ",\"hypotheses\":" ^ arr (jsonString o Parse.term_to_string) (Thm.hyp th) ^
           ",\"oracles\":" ^ arr jsonString oracles ^
           ",\"axiom_dependencies\":" ^ arr jsonString axioms ^ "}" end;
      val thy = current_theory ();
      val output = TextIO.openOut "kernel_report.json";
      val report = "{\"theory\":" ^ jsonString thy ^
        ",\"added_axioms\":" ^ arr entry (DB.axioms thy) ^
        ",\"definitions\":" ^ arr entry (DB.definitions thy) ^
        ",\"stored_theorems\":" ^ arr entry (DB.theorems thy) ^ "}";
    in TextIO.output (output, report); TextIO.closeOut output end;
    (* OPTIONAL_AST_INSPECTION *)
    OS.Process.exit OS.Process.success)
   handle e =>
     (TextIO.output (TextIO.stdErr, "Native HOL4 execution failed: " ^ General.exnMessage e ^ "\n");
      OS.Process.exit OS.Process.failure));
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--prover", choices=["hol4", "isabelle"], required=True)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--isabelle", default=str(Path.home() / "thick_training/tools/Isabelle2025-2.app/bin/isabelle"))
    ap.add_argument("--hol4", default=str(Path.home() / "thick_training/tools/HOL4-trindemossen-2/bin/hol"))
    ap.add_argument("--hol4-library", default=str(Path.home() / "thick_training/hol4_lib"),
                    help="Directory put on HOL4's loadPath, so a source may load deonticTheory; nothing is loaded for it")
    ap.add_argument("--driver-file", help="Explicit inspection harness; does not rewrite the supplied source")
    ap.add_argument("--export-ast", action="store_true", help="Export native terms after source execution, as a separate inspection step")
    args = ap.parse_args()
    if args.prover == "hol4":
        driver = Path(args.driver_file).read_text() if args.driver_file else HOL4_DRIVER
        if args.export_ast:
            marker = "(* OPTIONAL_AST_INSPECTION *)"
            if marker not in driver:
                raise SystemExit("Selected driver has no AST inspection hook")
            inspection = r'''(use "export_hol4_terms.sml" handle e =>
              let val stream = TextIO.openOut "ast_error.txt"
              in TextIO.output(stream, General.exnMessage e); TextIO.closeOut stream end);'''
            driver = driver.replace(marker, inspection, 1)
        # Make the optional deontic library loadable. The source decides whether to load it; nothing is opened for it.
        driver = f'val _ = loadPath := "{args.hol4_library}" :: !loadPath;\n' + driver
        Path("driver.sml").write_text(driver)
        command = [args.hol4, "--noconfig"]
        stdin = driver
        installation = Path(args.hol4).resolve().parent.parent
        commit = subprocess.run(["git", "-C", str(installation), "rev-parse", "HEAD"],
                                capture_output=True, text=True, check=True).stdout.strip()
        version = {"release": "trindemossen-2", "git_commit": commit, "executable": args.hol4}
        script = Path(args.hol4_library) / "deonticScript.sml"
        if script.exists():
            import hashlib
            version["deontic_library"] = {"dir": args.hol4_library, "deonticScript_sha256": hashlib.sha256(script.read_bytes()).hexdigest()}
    else:
        # The caller supplies the file's native theory name as its filename.
        files = list(Path.cwd().glob("*.thy"))
        if len(files) != 1:
            raise SystemExit("Supply exactly one native .thy file")
        source = files[0]
        command = [args.isabelle, "process_theories", "-O", "-U", "-l", "HOL", "-f", str(source), source.stem]
        stdin = None
        version_run = subprocess.run([args.isabelle, "version"], capture_output=True, text=True, check=True)
        version = {"release": version_run.stdout.strip(), "executable": args.isabelle}
    start = time.monotonic()
    env = dict(os.environ, HOL_NOCONFIG="1")
    with Path("native.log").open("w") as log:
        process = subprocess.Popen(command, stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                                   stdout=log, stderr=subprocess.STDOUT, text=True, env=env, start_new_session=True)
        timed_out = False
        try:
            process.communicate(stdin, timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
    result = {"prover": args.prover, "version": version, "command": command,
              "exit_code": process.returncode, "timed_out": timed_out,
              "elapsed_seconds": round(time.monotonic() - start, 3),
              "status": "timeout" if timed_out else "processed" if process.returncode == 0 else "execution_failed",
              "scope": "Native execution only. Added axioms are assumptions; execution does not establish their truth or consistency."}
    if Path("kernel_report.json").exists():
        result["kernel_report"] = json.loads(Path("kernel_report.json").read_text())
        if Path("kernel_binding_report.json").exists():
            result["kernel_report"]["theorem_values"] = json.loads(Path("kernel_binding_report.json").read_text())
        for kind in ("added_axioms", "definitions", "stored_theorems", "theorem_values"):
            for theorem in result["kernel_report"].get(kind, []):
                # DISK_THM denotes the standard trust in persisted library theorems.
                # Preserve every raw tag, while separating it from other oracle tags.
                theorem["non_library_oracle_tags"] = [tag for tag in theorem["oracles"] if tag != "DISK_THM"]
        # a theorem made without a proof (mk_thm or another oracle) is not a checked theorem: the source fails
        unproven = sorted({t.get("name", "?") for kind in ("stored_theorems", "theorem_values")
                           for t in result["kernel_report"].get(kind, []) if t.get("non_library_oracle_tags")})
        if unproven and result["status"] == "processed":
            result["status"] = "unproven_theorems"
            result["unproven_theorems"] = unproven
    if args.export_ast:
        result["ast_export_status"] = "exported" if Path("kernel_ast.json").exists() else "not_exported"
        if Path("ast_error.txt").exists():
            result["ast_export_status"] = "failed"
            result["ast_export_error"] = Path("ast_error.txt").read_text()
    Path("native_result.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
