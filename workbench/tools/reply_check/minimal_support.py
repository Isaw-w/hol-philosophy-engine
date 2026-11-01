"""Check every "because A, so B" step in a cited reply: is the cited item A part of some smallest support of the
cited theorem B? No model call; HOL4 decides each question.

  python3 tools/reply_check/minimal_support.py runs/DATE/REVIEW_RUN runs/DATE/ARGUMENT_RUN
      # needs REVIEW_RUN/citations/citations.json (reply_citations.py); writes REVIEW_RUN/minimal_support/

A smallest support of B is a set of starting points that gives B and from which no item can be left out. The starting
points are the argument's axioms and definitions, plus the premises the theorem B itself states (a theorem "P ==> C"
says "because P, C", so a cited axiom that gives P is a reason too) (Besnard and Hunter's "support"; a "justification" in axiom pinpointing). A citation group in the reply names
theorems (the conclusions B) and axioms or definitions (the reasons A). For each reason A the check asks whether A
belongs to some smallest support of some conclusion of a cited theorem. If it belongs to none, A is not a reason for
what the sentence concludes. If it belongs to one, A is a needed part of one way of getting B; whether it is the real
reason is left to the reader.

All smallest supports of each conclusion are found by the dualization loop: a support not found yet misses some
smallest hitting set of the found ones, so testing the complement of every such hitting set finds it, and when every
test fails the list is complete. Statements without numbers, lambdas or unbounded quantifiers are decided by SAT on
their propositional reading (each atom a letter); the rest by the shared rewriting and metis fallbacks.
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent))
from native_check import check                               # noqa: E402

ANALYSIS = r'''
val _ = let
  fun fetch n = DB.fetch "-" n
  val gamma = map (fn n => (n, fetch n)) DEF_NAMES @ DB.axioms (current_theory ())
  fun out s = TextIO.print ("SUPPORT|" ^ String.translate (fn #"\n" => " " | c => str c) s ^ "\n")
  fun minus a b = List.filter (fn x => not (List.exists (fn y => y = x) b)) a
  (* propositional after the finite expansion: then the SAT answer settles both directions *)
  fun plain t =
    let val e = expand_finite t
    in not (can (find_term (fn x => is_forall x orelse is_exists x orelse is_abs x orelse type_of x = numSyntax.num)) e) end
  (* the starting points for one theorem: the axioms and definitions, and the premises the theorem itself states *)
  val items = ref (map (fn (n, th) => (n, th, plain (concl th))) gamma)
  fun find n = valOf (List.find (fn (m, _, _) => m = n) (!items))
  fun gives names (g, g_plain) =
    let val ths = map (#2 o find) names
    in if g_plain andalso List.all (#3 o find) names then prop_follows ths g else follows_each [] ths g end
  fun supports pool g = all_smallest gives pool g      (* prop.sml *)
  fun numbered l = ListPair.zip (List.tabulate (length l, fn j => j + 1), l)
  val _ = List.app (fn n =>
      let val (_, b) = strip_forall (concl (fetch n))
          val (ants, cons) = if is_imp_only b then (strip_conj (fst (dest_imp_only b)), strip_conj (snd (dest_imp_only b)))
                             else ([], strip_conj b)
          val stated = map (fn (k, p) => ("premise " ^ Int.toString k, ASSUME p, plain p)) (numbered ants)
          val g_items = map (fn (m, th) => (m, th, plain (concl th))) gamma
          val _ = items := g_items @ stated
          (* a stated premise that says the same as an axiom or definition is merged into it: otherwise every such
             pair doubles the number of smallest supports *)
          fun same_as (k, th, pl) = List.find (fn (m, mth, mpl) => gives [m] (concl th, pl) andalso gives [k] (concl mth, mpl)) g_items
          val aliases = List.mapPartial (fn s => case same_as s of SOME (m, _, _) => SOME (#1 s, m) | NONE => NONE) stated
          val _ = List.app (fn (k, m) => out ("same|" ^ n ^ "|" ^ k ^ "|" ^ m)) aliases
          val pool = minus (map #1 (!items)) (map #1 aliases)
          val _ = List.app (fn (k, p) => out ("premise|" ^ n ^ "|" ^ Int.toString k ^ "|" ^ term_to_string p)) (numbered ants)
      in List.app (fn (j, c) =>
           let val key = n ^ "|" ^ Int.toString j
               val _ = out ("part|" ^ key ^ "|" ^ term_to_string c)
               val (ms, complete) = supports pool (c, plain c)
               val _ = List.app (fn m => out ("support|" ^ key ^ "|" ^ String.concatWith "," m)) ms
           in out ("complete|" ^ key ^ "|" ^ Bool.toString complete) end) (numbered cons) end)
    TARGETS
in () end;
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("review"); ap.add_argument("argument"); ap.add_argument("--host", default="mini")
    a = ap.parse_args()
    rv, arg = Path(a.review), Path(a.argument)
    rows = json.loads((rv / "citations/citations.json").read_text())["rows"]
    source = (arg / "native_check/source.sml").read_text()
    ast = json.loads((arg / "native_check/kernel_ast.json").read_text())
    def_names = re.findall(r"^Definition\s+([A-Za-z_][\w']*)(?:\[[^\]]*\])?\s*:", source, re.M)
    def_names += re.findall(r"^val\s+([A-Za-z_][\w']*)\s*=\s*(?:Define|xDefine|new_definition)\b", source, re.M)
    axiom_names = {t["name"] for t in ast.get("axioms", [])}
    theorems = {t["name"] for t in ast["theorems"]} - axiom_names - set(def_names)
    items = axiom_names | set(def_names)

    def item(n):                                  # a cited definition may drop its _def suffix
        return n if n in items else (n + "_def" if n + "_def" in items else None)

    groups = [r for r in rows if r["cites"] and r["cites"] != ["none"]]
    targets = sorted({c for r in groups for c in r["cites"] if c in theorems})
    analysis = ((HERE / "prop.sml").read_text() + "\n" + ANALYSIS
                .replace("DEF_NAMES", "[" + ", ".join(json.dumps(n) for n in def_names) + "]")
                .replace("TARGETS", "[" + ", ".join(json.dumps(n) for n in targets) + "]"))
    ends = list(re.finditer(r"val\s+_\s*=\s*export_theory\s*\(\s*\)\s*;", source))
    i = ends[-1].start() if ends else len(source)
    out = rv / "minimal_support"; out.mkdir(exist_ok=True)
    combined = out / "source_with_analysis.sml"
    combined.write_text(source[:i] + analysis + "\n" + source[i:])
    res = check(combined, out / "hol4", "hol4", a.host, timeout=3600)
    if res.get("status") != "processed":
        raise SystemExit(f"HOL4 did not process the analysis: {res.get('status')}")
    facts = [l.split("|")[1:] for l in (out / "hol4" / "native.log").read_text().splitlines() if l.startswith("SUPPORT|")]
    part_text, supports, complete, stated, same = {}, {}, {}, {}, {}
    for f in facts:
        if f[0] == "same":
            same[(f[1], int(f[2].split()[1]))] = f[3]; continue
        key = (f[1], int(f[2]))
        if f[0] == "premise":
            stated.setdefault(f[1], []).append((int(f[2]), "|".join(f[3:])))
        elif f[0] == "part":
            part_text[key] = "|".join(f[3:])
        elif f[0] == "support":
            supports.setdefault(key, []).append([x for x in f[3].split(",") if x])
        elif f[0] == "complete":
            complete[key] = f[3] == "true"

    L = [f"Smallest supports in {rv.name}, checked against {arg.name}", "",
         "For each cited reason: the cited conclusions it is part of a smallest support of.", ""]
    report, flagged, open_ = [], 0, 0
    for r in groups:
        thms = [c for c in r["cites"] if c in theorems]
        reasons = [c for c in r["cites"] if c not in theorems]
        L.append(f"[{r['i']}] {r['span']}")
        entry = {"i": r["i"], "span": r["span"], "conclusions": thms, "reasons": {}}
        if not thms:
            L.append("    cites no theorem: the sentence states premises, there is no step to check.")
        for c in reasons:
            n = item(c)
            if n is None:
                L.append(f"    {c}: not an axiom or definition of the argument"); entry["reasons"][c] = "unknown"; continue
            if not thms:
                continue
            hits = [f"{t} (conclusion {j})" for (t, j) in sorted(supports) if t in thms and any(n in s for s in supports[(t, j)])]
            done = all(complete.get(k, False) for k in part_text if k[0] in thms)
            if hits:
                verdict = "reason for " + ", ".join(hits)
            elif done:
                verdict = "NOT A REASON: in no smallest support of " + ", ".join(thms); flagged += 1
            else:
                verdict = "not found in a smallest support of " + ", ".join(thms) + " (the search stopped early, so not settled)"; open_ += 1
            L.append(f"    {c}: {verdict}")
            entry["reasons"][c] = verdict
        report.append(entry)
        L.append("")
    L.append(f"Reasons cited in no smallest support of their sentence's conclusions: {flagged}. Not settled: {open_}.")
    L.append("")
    L.append("Every smallest support of each cited conclusion (\"premise k\" is the theorem's own stated premise k):")
    for key in sorted(part_text):
        t, j = key
        ms = supports.get(key, [])
        if j == 1:
            L += [f"  {t}, stated premise {k}: {text}" + (f"  (the same as {same[(t, k)]}; merged into it)" if (t, k) in same else "")
                  for k, text in stated.get(t, [])]
        L.append(f"  {t}, conclusion {j}: {part_text[key]}")
        if not ms:
            L.append("      does not follow from the axioms and definitions")
        for m in ms:
            L.append("      {" + ", ".join(m) + "}")
        if not complete.get(key, False):
            L.append("      (search stopped early: there may be more)")
    (out / "minimal_support.txt").write_text("\n".join(L) + "\n")
    (out / "minimal_support.json").write_text(json.dumps({"groups": report, "facts": facts}, indent=1, ensure_ascii=False))
    print("\n".join(L))


if __name__ == "__main__":
    main()
