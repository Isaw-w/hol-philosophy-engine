"""Find every element of a HOL4 argument that plays no role in its final theorem. No model call.

  python3 role_check.py DIR [DIR ...]       # each DIR holds a source.sml with a Theorem `final`
  python3 role_check.py ESSAY               # every prose/s*/p* and formal/**/ directory of the essay

An argument (Besnard and Hunter 2001; Elements of Argumentation, 2008) is a consistent set of premises that entails
its claim and is minimal: no premise can be dropped. Minimality only bites at the level at which premises are cut,
so a premise that bundles two claims can carry one the argument never uses. This tool cuts first, then tests.

1. Formal elements (HOL4 and the workbench's Z3 engine, on the Mac mini). Every axiom is rewritten into its smallest
   pieces: conjunctions are split, also under implications and universal quantifiers ("P ==> A /\\ B" gives "P ==> A"
   and "P ==> B"; "!x. A x /\\ B x" gives "!x. A x" and "!x. B x"). Conditions (the parts before ==>) stay with their
   piece. HOL4 does the cutting and checks that each piece, written back as text, parses to the same term; the pieces
   become the axioms of a new source (each split axiom is then proved again from its pieces under its own name, so
   the source's own proofs run unchanged), and the Z3 engine finds every smallest set of
   pieces for each conclusion of `final`. A piece in none of them plays no role (Z3's "does not follow" answers count
   only when their countermodels hold up in HOL semantics; anything undecided is reported as unknown).
2. English elements (code, closed list). HOL4 does not read comments, so a gloss must be atomic: one predicate of its
   arguments, with every connective, negation, quantifier and clause written in the formula instead. Flagged: commas,
   colons, semicolons, dashes, parentheses; and, or, nor, but (except "and" between personal names); not, no, never,
   nowhere, nothing, none, neither, without; only, solely, merely, each, every, all, any, some; rather than, as
   opposed to, instead of, as when, in the way; that, which, who, whom, whose, what, how, where, when, because,
   though, although, if, unless, while. Each flagged part is an element HOL4 cannot test. A quotation
   gloss should be only "Name verb that [Qn]" or "Name verb: [Qn]"; anything else in its frame is listed too. Each
   listed part must either be formalized as its own piece (and then step 1 decides) or be accepted by the user.

Writes DIR/role_check/report.txt for each DIR and prints a summary.
"""
import json, re, shutil, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HOL = Path("/Users/cy/Desktop/Fun/possibility_calculator/Learn/experiments/moral-reasoning/experiments/data/"
           "thick_training/difficult_advice_v2/cloud_gen/hol")
sys.path.insert(0, str(HOL / "tools"))
from native_check import check  # noqa: E402

ANALYSIS = r'''
val imp_conj_split = prove (``!P Q R. (P ==> Q /\ R) = ((P ==> Q) /\ (P ==> R))``, metis_tac []);
val forall_and_split = prove (``!P Q. (!x:'a. P x /\ Q x) = ((!x. P x) /\ (!x. Q x))``, metis_tac []);
val _ = let
  fun out s = TextIO.print ("ROLE|" ^ String.translate (fn #"\n" => " " | c => str c) s ^ "\n")
  val axs = List.filter (fn (n, _) => n <> "imp_conj_split" andalso n <> "forall_and_split") (DB.axioms (current_theory ()))
  fun split th = CONJUNCTS (SIMP_RULE pure_ss [imp_conj_split, forall_and_split] th)
                 handle _ => CONJUNCTS th
  fun name_pieces (n, th) =
    let val ps = split th
    in if length ps = 1 then [(n, n, hd ps)]
       else ListPair.map (fn (i, p) => (n, n ^ "_" ^ Int.toString i, p)) (List.tabulate (length ps, fn i => i + 1), ps) end
  fun text t = with_flag (show_types, true) term_to_string t
  fun back s t = (aconv (Parse.Term [QUOTE s]) t) handle _ => false
in List.app (fn (a, n, p) => let val s = text (concl p)
                             in out ("piece|" ^ a ^ "|" ^ n ^ "|" ^ Bool.toString (back s (concl p)) ^ "|" ^ s) end)
            (List.concat (map name_pieces axs)) end;
'''

MARKERS = [r",", r";", r":", r"\(", r"\s[-–—]+\s",
           r"(?<![A-Z][a-z])(?<![A-Z][a-z][a-z])(?<![A-Z][a-z]{3})(?<![A-Z][a-z]{4})(?<![A-Z][a-z]{5})\s+and\b(?!\s+[A-Z])",
           r"\bor\b", r"\bnor\b", r"\bbut\b",
           r"\bnot\b", r"\bno\b", r"\bnever\b", r"\bnowhere\b", r"\bnothing\b", r"\bnone\b", r"\bneither\b",
           r"\bwithout\b", r"\bonly\b", r"\bsolely\b", r"\bmerely\b", r"\beach\b", r"\bevery\b", r"\ball\b",
           r"\bany\b", r"\bsome\b", r"\brather than\b", r"\bas opposed to\b", r"\binstead of\b", r"\bas when\b",
           r"\bin the way\b", r"\bthat\b", r"\bwhich\b", r"\bwho\b", r"\bwhom\b", r"\bwhose\b", r"\bwhat\b",
           r"\bhow\b", r"\bwhere\b", r"\bwhen\b", r"\bbecause\b", r"\bthough\b", r"\balthough\b", r"\bif\b",
           r"\bunless\b", r"\bwhile\b"]
SPLIT = re.compile("|".join(MARKERS))


def gloss_elements(src):
    """(constant, gloss, [extra parts]) for every gloss with more than one assertion."""
    out = []
    declared = set(re.findall(r'new_constant\s*\(\s*"(\w+)"', src))
    for m in re.finditer(r"\(\*\s*([A-Z]\w*)(?:\s+\w)*\s*:\s*(.*?)\s*\*\)", src):
        c, g = m[1], m[2]
        if c not in declared:                   # a file's description comment, not a gloss
            continue
        body = g
        q = re.search(r"\s*(?:that|:)?\s*\[Q\d+\]\s*$", g)
        if q:                                   # a quotation gloss: only its frame is the AI's
            body = g[: q.start()]
        cuts = [x.start() for x in SPLIT.finditer(body)]
        if cuts:
            parts = [body[a:b].strip(" ,;:") for a, b in zip(cuts, cuts[1:] + [len(body)])]
            out.append((c, g, [p for p in parts if p]))
    return out


AXIOM = re.compile(r'val\s+(\w+)\s*=\s*new_axiom\s*\(\s*"(\w+)"\s*,\s*``(.*?)``\s*\)\s*;', re.S)


def split_source(src, pieces):
    """the source with each split axiom replaced by its pieces (as axioms) and then proved again from them under its
    own name, so that every later proof in the source runs unchanged; None if an axiom cannot be found in the text"""
    by_parent = {}
    for parent, name, term in pieces:
        by_parent.setdefault(parent, []).append((name, term))
    found = {m[2] for m in AXIOM.finditer(src)}
    if any(len(ps) > 1 and parent not in found for parent, ps in by_parent.items()):
        return None

    def replace(m):
        ps = by_parent.get(m[2], [])
        if len(ps) <= 1:
            return m[0]
        body = "".join(f'val {n} = new_axiom ("{n}", ``{t}``);\n' for n, t in ps)
        return body + f"val {m[1]} = prove (``{m[3]}``, metis_tac [{', '.join(n for n, _ in ps)}]);"
    return AXIOM.sub(replace, src)


def run(d):
    d = Path(d).resolve()
    work = d / "role_check"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir()
    src = (d / "source.sml").read_text()
    body = re.sub(r"val _ = export_theory \(\);\s*$", "", src.rstrip())
    (work / "source.sml").write_text(body + "\n\n" + ANALYSIS + "\nval _ = export_theory ();\n")
    r = check(work / "source.sml", work / "native", "hol4", "mini", timeout=900)
    log = (work / "native" / "native.log").read_text() if (work / "native" / "native.log").exists() else ""
    rows = [l.split("|", 5)[2:] for l in log.splitlines() if l.startswith("ROLE|piece|")]
    pieces = [(a, n, t) for a, n, ok, t in rows]
    unreadable = [n for a, n, ok, t in rows if ok != "true"]
    lines = [f"{d}", f"HOL4 cutting: {r.get('status')} exit {r.get('exit_code')}; pieces: {len(pieces)}"]
    no_role, ok_all = [], False
    if unreadable:
        lines.append(f"  pieces that do not parse back to the same term (not tested): {unreadable}")
    elif pieces and split_source(src, pieces):
        sd = work / "split"; sd.mkdir()
        (sd / "source.sml").write_text(split_source(src, pieces))
        r2 = check(sd / "source.sml", sd / "native_check", "hol4", "mini", timeout=900)
        log2 = (sd / "native_check" / "native.log").read_text() if (sd / "native_check" / "native.log").exists() else ""
        if "val final =" not in log2:
            lines.append("  HOL4 could not prove final from the pieces: " + log2[-1500:])
        else:
            subprocess.run([sys.executable, "tools/reply_check/z3_engine.py", str(sd)], cwd=HOL, capture_output=True, text=True)
            zj = sd / "z3_engine" / "z3_engine.json"
            if zj.exists():
                z = json.loads(zj.read_text())
                complete = all(c.get("complete") for c in z["conclusions"])
                no_role = [s.removeprefix("axiom ") for s in z["isolated"]]
                ok_all = complete and z.get("isolated_settled", True)
                lines.append(f"  Z3 engine: every list complete: {complete}; consistent: {z['consistent']}; "
                             f"countermodels held in HOL semantics: {z['countermodels'].get('validated', 0)}, "
                             f"did not: {z['countermodels'].get('not validated', 0)}")
            else:
                lines.append("  Z3 engine gave no result")
    lines.append(f"playing no role: {len(no_role)}")
    lines += [f"  NO ROLE {n}: {next((t for _, m, t in pieces if m == n), '')}" for n in no_role]
    gl = gloss_elements(src)
    lines.append(f"glosses with more than one assertion: {len(gl)}")
    for c, g, parts in gl:
        lines.append(f"  {c}: \"{g}\"")
        lines += [f"      part: {p}" for p in parts]
    (work / "report.txt").write_text("\n".join(lines) + "\n")
    return d, ok_all, no_role, len(gl), lines


def main(args):
    dirs = []
    for a in args:
        p = Path(a).resolve()
        if (p / "source.sml").exists():
            dirs.append(p)
        else:
            dirs += sorted(q.parent for q in list(p.glob("prose/s*/p*/source.sml")) + list(p.glob("formal/**/source.sml"))
                           if not {"role_check", "native_check", "native", "argument_checks", "hidden_premises", "isolated_parts",
                                    "gloss_claims"} & set(q.parts))
    with ThreadPoolExecutor(max_workers=9) as ex:
        results = list(ex.map(run, dirs))
    for d, ok, no_role, n_gl, _ in results:
        print(f"{'OK ' if ok else 'ERR'} {d.relative_to(Path.cwd()) if d.is_relative_to(Path.cwd()) else d}: "
              f"{len(no_role)} formal pieces with no role {no_role}; {n_gl} glosses with extra parts")


if __name__ == "__main__":
    main(sys.argv[1:])
