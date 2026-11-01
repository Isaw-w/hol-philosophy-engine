"""Deterministic structural verbalization of native HOL4 terms.

  python3 tools/verbalize_hol4.py response.json --out checks/fresh-verbalization

HOL4 parses, type-checks and executes the unchanged source. Native kernel term
destructors export its theorem statements. This program renders that AST using
fixed templates, retains unknown symbols, and makes no model calls. It is not
a formally verified translator or a semantic interpretation of symbol names.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import uuid

HERE = Path(__file__).resolve().parent
STATEMENT_KINDS = ("axioms", "definitions", "theorems", "theorem_values")
DRIVER = '''val _ =
  ((use "source.sml"; use "export_hol4_terms.sml"; OS.Process.exit OS.Process.success)
   handle e => (TextIO.output (TextIO.stdErr, General.exnMessage e ^ "\\n");
                OS.Process.exit OS.Process.failure));
'''


def application(node):
    args = []
    while node["kind"] == "application":
        args.append(node["argument"])
        node = node["function"]
    return node, list(reversed(args))


def logical(node, name, arity):
    head, args = application(node)
    theory = "min" if name in ("==>", "=") else "bool"
    if (head["kind"] == "constant" and head["theory"] == theory
            and head["name"] == name and len(args) == arity):
        return args
    return None


def type_text(node):
    if node["kind"] == "type_variable":
        return node["name"]
    args = node["arguments"]
    if node["theory"] == "min" and node["name"] == "bool" and not args:
        return "truth value"
    if node["theory"] == "min" and node["name"] == "fun" and len(args) == 2:
        return "(" + type_text(args[0]) + " -> " + type_text(args[1]) + ")"
    base = node["theory"] + "$" + node["name"]
    return base + ("[" + ", ".join(map(type_text, args)) + "]" if args else "")


def expression(node):
    kind = node["kind"]
    if kind == "variable":
        return node["name"]
    if kind == "constant":
        return node["theory"] + "$" + node["name"]
    if kind == "abstraction":
        return "the function mapping " + node["variable"]["name"] + " to (" + expression(node["body"]) + ")"
    head, args = application(node)
    head_text = expression(head)
    if head["kind"] not in ("variable", "constant"):
        head_text = "(" + head_text + ")"
    return head_text + "(" + ", ".join(expression(a) for a in args) + ")"


def term_type(node):
    if node["kind"] in ("variable", "constant"):
        return node["type"]
    if node["kind"] == "abstraction":
        return {"kind": "type_application", "theory": "min", "name": "fun",
                "arguments": [node["variable"]["type"], term_type(node["body"])]}
    function_type = term_type(node["function"])
    if (function_type and function_type.get("theory") == "min"
            and function_type.get("name") == "fun" and len(function_type.get("arguments", [])) == 2):
        return function_type["arguments"][1]
    return None


# The optional deontic library (tools/hol4_libraries/deontic): fixed phrases for its operators. A statement there has type world -> bool.
DEONTIC = {"OughtNow": (1, "it ought now to be that {0}"), "Ought": (2, "it ought to be that {0}, given {1}"),
           "Can": (1, "{0} can still come about"), "Settled": (1, "{0} is settled"),
           "Knows": (1, "the assistant knows {0}"), "Better": (2, "{0} is better than {1}")}


def deontic(node):
    head, args = application(node)
    if head["kind"] == "constant" and head["theory"] == "deontic":
        return head["name"], args
    return None, args


def lifted(body, x):
    """a statement written pointwise, \\x. ..., as a phrase: names applied to x, not, and, or, if-then; None if not of that shape"""
    head, args = application(body)
    if head["kind"] in ("variable", "constant") and len(args) == 1 and args[0]["kind"] == "variable" and args[0]["name"] == x:
        return head["name"]
    if head["kind"] == "abstraction" and len(args) == 1 and args[0]["kind"] == "variable" and args[0]["name"] == x:
        return lifted(head["body"], head["variable"]["name"])        # (\y. ...) x, left unreduced by HOL4: read as written
    if logical(body, "T", 0) is not None:
        return "anything at all"
    negated = logical(body, "~", 1)
    if negated:
        inner = lifted(negated[0], x)
        return None if inner is None else "not " + (inner if " " not in inner else "(" + inner + ")")
    for name, word in (("/\\", " and "), ("\\/", " or ")):
        parts = logical(body, name, 2)
        if parts:
            a, b = lifted(parts[0], x), lifted(parts[1], x)
            if a is not None and b is not None:
                return a + word + b
            return None
    parts = logical(body, "==>", 2)
    if parts:
        a, b = lifted(parts[0], x), lifted(parts[1], x)
        return None if a is None or b is None else "if " + a + " then " + b
    return None


def statement(node):
    """a world -> bool term as a phrase: a name, a pointwise combination of names, a library operator, or the raw expression"""
    if node["kind"] in ("variable", "constant") and node.get("theory") != "deontic":
        return node["name"]
    if node["kind"] == "abstraction":
        x, body = node["variable"]["name"], node["body"]
        phrase = lifted(body, x)
        if phrase is not None:
            return phrase if " " not in phrase else "(" + phrase + ")"
        return "the statement true at " + x + " when (" + expression(body) + ")"
    name, args = deontic(node)
    if name in DEONTIC and len(args) == DEONTIC[name][0]:
        return "(" + DEONTIC[name][1].format(*[statement(a) for a in args]) + ")"
    return expression(node)


def render(node, path="/", depth=0):
    """Every output segment retains a pointer to the native AST it describes."""
    def line(text, rule, at=path, level=depth):
        return {"depth": level, "text": text, "ast_path": at, "rule": rule}

    for name, label in [("!", "For every"), ("?", "There exists")]:
        args = logical(node, name, 1)
        if args and args[0]["kind"] == "abstraction":
            variables, body, body_path = [], node, path
            while True:
                nested = logical(body, name, 1)
                if not nested or nested[0]["kind"] != "abstraction":
                    break
                abstraction = nested[0]
                variables.append(abstraction["variable"])
                body = abstraction["body"]
                body_path = body_path.rstrip("/") + "/argument/body"
            types = [type_text(v["type"]) for v in variables]
            if len(set(types)) == 1:
                names = ", ".join(v["name"] for v in variables) + " of type " + types[0]
            else:
                names = ", ".join(v["name"] + " of type " + t for v, t in zip(variables, types))
            return [line(label + " " + names + ":", name)] + render(body, body_path, depth + 1)
    args = logical(node, "==>", 2)
    if args:
        prefix = path.rstrip("/")
        return ([line("If:", "implication_antecedent")]
                + render(args[0], prefix + "/function/argument", depth + 1)
                + [line("Then:", "implication_consequent")]
                + render(args[1], prefix + "/argument", depth + 1))
    for name, label in [("/\\", "Both of the following:"), ("\\/", "At least one of the following:")]:
        args = logical(node, name, 2)
        if args:
            def flatten(n, at):
                nested = logical(n, name, 2)
                if nested:
                    prefix = at.rstrip("/")
                    return flatten(nested[0], prefix + "/function/argument") + flatten(nested[1], prefix + "/argument")
                return [(n, at)]
            segments = [line("All of the following:" if name == "/\\" else label, name)]
            for child, child_path in flatten(node, path):
                segments.extend(render(child, child_path, depth + 1))
            return segments
    args = logical(node, "~", 1)
    if args:
        return [line("It is not the case that:", "negation")] + render(
            args[0], path.rstrip("/") + "/argument", depth + 1)
    args = logical(node, "=", 2)
    if args:
        boolean = {"kind": "type_application", "theory": "min", "name": "bool", "arguments": []}
        if term_type(args[0]) == boolean and term_type(args[1]) == boolean:
            prefix = path.rstrip("/")
            return ([line("The following statements are equivalent:", "boolean_equivalence")]
                    + render(args[0], prefix + "/function/argument", depth + 1)
                    + render(args[1], prefix + "/argument", depth + 1))
        return [line("The value of (" + expression(args[0]) + ") equals the value of (" + expression(args[1]) + ").", "equality")]
    if logical(node, "T", 0) is not None:
        return [line("True.", "truth")]
    if logical(node, "F", 0) is not None:
        return [line("False.", "falsehood")]
    name, args = deontic(node)
    if name == "Valid" and len(args) == 1:
        return [line("In every situation: " + statement(args[0]) + ".", "deontic_valid")]
    if name == "Now" and len(args) == 1:
        return [line("In the actual situation: " + statement(args[0]) + ".", "deontic_now")]
    if name in DEONTIC and len(args) == DEONTIC[name][0] + 1:
        phrase = DEONTIC[name][1].format(*[statement(a) for a in args[:-1]])
        return [line("At " + expression(args[-1]) + ", " + phrase + ".", "deontic_" + name)]
    return [line("The expression (" + expression(node) + ") is true.", "uninterpreted_expression")]


def verbalize(document, located_only=False):
    sections, trace = [], []
    entries = []
    for kind in STATEMENT_KINDS:
        for index, theorem in enumerate(document.get(kind, [])):
            location = theorem.get("source_location") or {}
            if located_only and kind != "axioms" and not location.get("exact"):
                continue
            entries.append((kind, index, theorem))
    if located_only:
        entries.sort(key=lambda entry: ((entry[2].get("source_location") or {}).get("file", ""),
                                       (entry[2].get("source_location") or {}).get("line", -1)))
    for kind, index, theorem in entries:
        label = "Theorem value" if kind == "theorem_values" else kind[:-1].capitalize()
        title = label + ": " + theorem["name"]
        sections.append(title)
        base_path = "/" + kind + "/" + str(index)
        if theorem["hypotheses"]:
            sections.append("Under these undischarged hypotheses:")
            for j, hyp in enumerate(theorem["hypotheses"]):
                segments = render(hyp, base_path + "/hypotheses/" + str(j), 1)
                trace.extend(segments)
                sections.extend("  " * s["depth"] + s["text"] for s in segments)
        segments = render(theorem["conclusion"], base_path + "/conclusion")
        trace.extend(segments)
        sections.extend("  " * s["depth"] + s["text"] for s in segments)
        sections.append("")
    return "\n".join(sections), trace


def write_outputs(ast_file, out):
    """Render an existing native AST. Does not execute source or call a model."""
    out = Path(out)
    document = json.loads(Path(ast_file).read_text())
    text, trace = verbalize(document)
    (out / "controlled_english.txt").write_text(text)
    (out / "render_trace.json").write_text(json.dumps(trace, indent=2))
    located, located_trace = verbalize(document, located_only=True)
    (out / "source_declarations_english.txt").write_text(
        "SOURCE-LOCATED VIEW: axioms plus statements with exact native source locations.\n"
        "Statements without exact locations are retained in controlled_english.txt.\n\n" + located)
    (out / "source_declarations_trace.json").write_text(json.dumps(located_trace, indent=2))
    (out / "verbalize_hol4.py").write_bytes(Path(__file__).read_bytes())
    result = {"status": "rendered", "method": "fixed templates over native typed HOL4 terms",
              "model_calls": 0, "prover_calls_during_rendering": 0,
              "full_statement_count": sum(len(document.get(k, [])) for k in STATEMENT_KINDS),
              "source_view_statement_count": sum(1 for k in STATEMENT_KINDS
                  for t in document.get(k, []) if k == "axioms" or (t.get("source_location") or {}).get("exact")),
              "theorem_value_count": len(document.get("theorem_values", [])),
              "binding_inspection": document.get("binding_inspection"),
              "full_output": "controlled_english.txt", "source_view": "source_declarations_english.txt",
              "limitations": "Symbol meanings are not inferred. Source-located view may omit unlocated authored statements; full output retains them. Translator is not formally verified."}
    (out / "verbalization_result.json").write_text(json.dumps(result, indent=2))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source")
    ap.add_argument("--out", required=True)
    ap.add_argument("--host", default="mini")
    ap.add_argument("--block", type=int)
    ap.add_argument("--from-ast", action="store_true", help="Render an already exported native AST without executing source")
    args = ap.parse_args()
    source, out = Path(args.source).resolve(), Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    raw = source.read_bytes()
    (out / "original").mkdir()
    (out / "original" / source.name).write_bytes(raw)
    (out / "verbalize_hol4.py").write_bytes(Path(__file__).read_bytes())
    if args.from_ast:
        document = json.loads(raw)
        (out / "kernel_ast.json").write_bytes(raw)
        write_outputs(out / "kernel_ast.json", out)
        (out / "manifest.json").write_text(json.dumps({
            "source_ast": str(source), "source_ast_sha256": hashlib.sha256(raw).hexdigest(),
            "method": "Fixed structural templates over an existing native HOL4 AST; boolean association and consecutive same-kind quantifiers are flattened for presentation",
            "model_calls": 0, "prover_calls": 0,
            "limitations": "No symbol meanings inferred; translator has not been formally verified."}, indent=2))
        print(out / "controlled_english.txt")
        return
    text = raw.decode()
    if source.suffix == ".json":
        record = json.loads(text)
        if record.get("finish") == "content_filter":
            raise SystemExit("Provider filtered the response; no verbalization attempted")
        text = record.get("content")
        if not isinstance(text, str):
            raise SystemExit("No text content in response")
    if source.suffix.lower() in (".sml", ".ml"):
        code, transformation = text, {"kind": "native_source_identity"}
    else:
        from native_check import source_of
        code, transformation = source_of(text, args.block)
    if not code.strip():
        raise SystemExit("No source to execute")
    (out / "source.sml").write_text(code)
    (out / "verbalize_driver.sml").write_text(DRIVER)
    for name in ("native_worker.py", "export_hol4_terms.sml"):
        (out / name).write_bytes((HERE / name).read_bytes())
    remote = "thick_training/native_hol_checks/" + uuid.uuid4().hex
    manifest = {"original_file": str(source), "original_sha256": hashlib.sha256(raw).hexdigest(),
                "executed_source_sha256": hashlib.sha256(code.encode()).hexdigest(),
                "source_transformation": transformation, "source_rewritten": False,
                "host": args.host, "remote_directory": remote, "model_calls": 0,
                "method": "Native HOL4 kernel AST plus fixed structural English templates; no symbol meanings inferred",
                "limitations": "Not a formally verified translator. Unknown symbol meanings remain uninterpreted. No claim of equivalence between a supplied English gloss and a formal predicate."}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2))
    subprocess.run(["ssh", args.host, "mkdir -p " + shlex.quote(remote)], check=True)
    names = ["source.sml", "verbalize_driver.sml", "native_worker.py", "export_hol4_terms.sml"]
    subprocess.run(["scp", "-q", *[str(out / n) for n in names], args.host + ":" + remote + "/"], check=True)
    run = subprocess.run(["ssh", args.host, "cd " + shlex.quote(remote)
                          + " && python3 native_worker.py --prover hol4 --driver-file verbalize_driver.sml"],
                         capture_output=True, text=True)
    (out / "transport.log").write_text(run.stdout + run.stderr)
    run.check_returncode()
    for name in ("native_result.json", "native.log"):
        subprocess.run(["scp", "-q", args.host + ":" + remote + "/" + name, str(out / name)], check=True)
    result = json.loads((out / "native_result.json").read_text())
    if result["status"] != "processed":
        raise SystemExit("Source did not execute; see native.log. No source repair attempted.")
    subprocess.run(["scp", "-q", args.host + ":" + remote + "/kernel_ast.json", str(out / "kernel_ast.json")], check=True)
    document = json.loads((out / "kernel_ast.json").read_text())
    write_outputs(out / "kernel_ast.json", out)
    print(json.dumps({"theory": document["theory"], "theorems": len(document["theorems"]),
                      "model_calls": 0, "output": str(out / "controlled_english.txt")}, indent=2))


if __name__ == "__main__":
    main()
