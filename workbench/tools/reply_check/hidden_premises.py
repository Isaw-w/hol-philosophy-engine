"""Find every premise the final theorem rests on but does not state. No model call.

  python3 tools/reply_check/hidden_premises.py runs/DATE/RUN          # writes RUN/hidden_premises/

HOL4 is sound, so a checked theorem follows only from (a) the premises it states, (b) HOL4's own logic and arithmetic,
and (c) what the source itself introduced: definitions, type declarations, new constants and axioms. So everything the
final theorem rests on beyond (a) and (b) is in (c), and this tool lists all of it. It does not depend on which kind of
reasoning the source uses:

  A. Axioms the source added (always premises).
  B. Definitions: each of the source's definitions is left out in turn; if the final theorem no longer follows, it is
     a premise.
  C. The smallest pieces: every needed definition is cut into pieces (each clause; an "if and only if" into its two
     directions; a record into its fields; numbers into which is larger than which) wherever the theorem still follows
     from the pieces (otherwise the definition stays whole), every piece the proof can do without is dropped, and
     HOL4 checks that the rest suffices and that each remaining piece is needed. Then every other smallest set is found
     too (prop.sml, all_smallest), so items that can stand in for each other are all listed.
  D. Undefined terms: constants the source declared without defining them. Their meaning is only their name and
     comment.
  E. Closed lists: where a written list stands for "all the arguments", it is taken to be complete.
  F. Readings: HOL4 does not read comments; each symbol is taken to mean its comment.

What it cannot list: a step from the final theorem to a conclusion that is not written in HOL4.
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent))
from gloss_claims import glosses, split_imp, strip_comb      # noqa: E402
from plain_english import Plain, sentence                    # noqa: E402
from native_check import check                               # noqa: E402

ANALYSIS = r'''
val _ = let
  fun fetch n = DB.fetch "-" n
  val names = DEF_NAMES
  val extra = [DISJ_IMP_THM, FORALL_AND_THM]
  val _ = (metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ()
  fun out s = TextIO.print ("HIDDEN|" ^ String.translate (fn #"\n" => " " | c => str c) s ^ "\n")
  (* two generic proofs; a theorem counts as following if either succeeds. asms are given as assumptions *)
  fun by_rw asms ths g = (TAC_PROOF ((map concl asms, g),
        rw (ths @ extra) >> rpt (FIRST [decide_tac, metis_tac (asms @ ths)])); true) handle _ => false
  fun by_metis asms ths g = (TAC_PROOF ((map concl asms, g), rpt strip_tac >> metis_tac (asms @ ths)); true)
                            handle _ => false
  fun follows asms ths g = follows_each asms ths g
  val goal = concl FINAL_THM
  val defs = map (fn n => (n, fetch n)) names @
             map (fn (n, th) => ("axiom " ^ n, th)) (DB.axioms (current_theory ()))
  val _ = out ("baseline|" ^ Bool.toString (follows [] (map #2 defs) goal))
  val needed = List.filter (fn (n, _) =>
      let val ok = not (follows [] (map #2 (List.filter (fn (m, _) => m <> n) defs)) goal)
      in out ("needed|" ^ n ^ "|" ^ Bool.toString ok); ok end) defs
  (* cut each needed definition into its smallest pieces *)
  fun field_pieces tag l c =
    let val fields = map fst (TypeBase.fields_of (type_of l)) handle _ => []
        fun fact f = SOME (tag ^ "." ^ f, GEN_ALL (SIMP_CONV (srw_ss ()) [c]
                       (Parse.Term [QUOTE ("(" ^ term_to_string l ^ ")." ^ f)]))) handle _ => NONE
    in List.mapPartial fact fields end
  fun clause_pieces (n, i, c) =
    let val (l, r) = dest_eq (concl c)
        val tag = n ^ "#" ^ Int.toString i
    in if type_of l = bool then
         let val (a, b) = EQ_IMP_RULE c in [(tag ^ ".only_if", GEN_ALL a), (tag ^ ".if", GEN_ALL b)] end
       else case field_pieces tag l c of [] => [(tag, GEN_ALL c)] | fs => fs end
    handle _ => [(n ^ "#" ^ Int.toString i, GEN_ALL c)]
  fun pieces_of (n, th) =
    let val cs = map SPEC_ALL (CONJUNCTS (SPEC_ALL th))
    in List.concat (ListPair.map (fn (i, c) => clause_pieces (n, i, c)) (List.tabulate (length cs, fn i => i + 1), cs)) end
  (* replace a definition by its pieces only where the theorem still follows; otherwise keep it whole *)
  val items = List.foldl (fn ((n, th), items) =>
      let val ps = pieces_of (n, th)
          val trial = List.filter (fn (m, _) => m <> n) items @ ps
      in if length ps > 1 andalso follows [] (map #2 trial) goal then trial else items end) defs defs
  (* start from every definition and axiom, not only the individually needed ones: two items that can stand in for
     each other are each "not needed" alone, yet the theorem needs one of them *)
  (* numbers become the order between them *)
  fun value (_, th) = rhs (snd (strip_forall (concl th)))
  fun field_term (_, th) = lhs (snd (strip_forall (concl th)))
  fun is_num p = (type_of (value p) = numSyntax.num andalso numSyntax.is_numeral (value p)) handle _ => false
  val (numeric, other) = List.partition is_num items
  val orders = List.concat (map (fn a => List.mapPartial (fn b =>
      if numSyntax.int_of_term (value a) < numSyntax.int_of_term (value b) then
        SOME (#1 a ^ " < " ^ #1 b, TAC_PROOF (([], numSyntax.mk_less (field_term a, field_term b)), rw (map #2 numeric)))
      else NONE handle _ => NONE) numeric) numeric)
  val use_orders = not (null orders) andalso follows (map #2 orders) (map #2 other) goal
  val start = if use_orders then map (fn p => (true, p)) orders @ map (fn p => (false, p)) other
              else map (fn p => (false, p)) items
  (* a kept item is (given as an assumption?, (name, theorem)) *)
  fun holds keep = follows (map (#2 o #2) (List.filter #1 keep)) (map (#2 o #2) (List.filter (not o #1) keep)) goal
  val _ = out ("pieces_suffice|" ^ Bool.toString (holds start))
  val _ = out ("orders_used|" ^ Bool.toString use_orders)
  val kept = List.foldl (fn (c, keep) =>
      let val rest = List.filter (fn k => #1 (#2 k) <> #1 (#2 c)) keep
      in if holds rest then rest else keep end) start start
  val _ = out ("set_suffices|" ^ Bool.toString (holds kept))
  val _ = List.app (fn k => out ("each_needed|" ^ #1 (#2 k) ^ "|" ^
            Bool.toString (not (holds (List.filter (fn u => #1 (#2 u) <> #1 (#2 k)) kept))))) kept
  (* every smallest set of pieces that gives the theorem (prop.sml, all_smallest); what the other sets have that the
     first one lacks can stand in for it *)
  fun by_name ns = List.filter (fn k => List.exists (fn n => n = #1 (#2 k)) ns) start
  val (all_sets, all_done) = all_smallest (fn ns => fn _ => holds (by_name ns)) (map (#1 o #2) start) goal
  val _ = List.app (fn ns => out ("support_set|" ^ String.concatWith "," ns)) all_sets
  val _ = out ("supports_complete|" ^ Bool.toString all_done)
  val kept_names = map (#1 o #2) kept
  val _ = List.app (fn n => out ("alternative|" ^ n))
            (Lib.mk_set (List.filter (fn n => not (List.exists (fn m => m = n) kept_names)) (List.concat all_sets)))
  fun save (i, (_, (name, th))) =
    (save_thm ("piece_" ^ Int.toString i, th); out ("piece|piece_" ^ Int.toString i ^ "|" ^ name))
in List.app save (ListPair.zip (List.tabulate (length kept, fn i => i + 1), kept)) end;
'''


def lists_in(node, render):
    """every (head, term, written list) in an application whose last argument is a list literal"""
    found = []
    def walk(n):
        h, args = strip_comb(n)
        if h["kind"] == "constant" and h["name"] in ("CONS", "NIL"):
            return
        if h["kind"] == "constant" and args:
            last = strip_comb(args[-1])[0]
            if last["kind"] == "constant" and last["name"] in ("CONS", "NIL"):
                found.append((h["name"].split(".")[-1], render(args[0]) if len(args) > 1 else "", render(args[-1])))
        for a in args:
            walk(a)
        if n["kind"] == "abstraction":
            walk(n["body"])
    walk(node)
    return found


def symbols(node, acc):
    if node["kind"] in ("variable", "constant"):
        acc.add((node["kind"], node["name"].split(".")[-1], node.get("theory")))
    elif node["kind"] == "application":
        symbols(node["function"], acc); symbols(node["argument"], acc)
    elif node["kind"] == "abstraction":
        symbols(node["variable"], acc); symbols(node["body"], acc)
    return acc


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--final", default="final"); ap.add_argument("--host", default="mini")
    a = ap.parse_args()
    run = Path(a.run); nc = run / "native_check"
    source = (nc / "source.sml").read_text()
    notation, views = glosses(source)
    # the source's own definitions, by the names it gave them (pattern-matching ones are stored as theorems)
    def_names = re.findall(r"^Definition\s+([A-Za-z_][\w']*)(?:\[[^\]]*\])?\s*:", source, re.M)
    def_names += re.findall(r"^val\s+([A-Za-z_][\w']*)\s*=\s*(?:Define|xDefine|new_definition)\b", source, re.M)
    analysis = (HERE / "prop.sml").read_text() + "\n" + ANALYSIS.replace("DEF_NAMES", "[" + ", ".join(json.dumps(n) for n in def_names) + "]").replace("FINAL_THM", a.final)
    ends = list(re.finditer(r"val\s+_\s*=\s*export_theory\s*\(\s*\)\s*;", source))
    i = ends[-1].start() if ends else len(source)
    out = run / "hidden_premises"; out.mkdir(exist_ok=True)
    combined = out / "source_with_analysis.sml"
    combined.write_text(source[:i] + analysis + "\n" + source[i:])
    res = check(combined, out / "hol4", "hol4", a.host, timeout=1800)
    if res.get("status") != "processed":
        raise SystemExit(f"HOL4 did not process the analysis: {res.get('status')}")
    log = (out / "hol4" / "native.log").read_text()
    facts = [l.split("|")[1:] for l in log.splitlines() if l.startswith("HIDDEN|")]
    kast = json.loads((out / "hol4" / "kernel_ast.json").read_text())
    defs = {d["name"]: d for d in kast["definitions"]}
    r = Plain(notation, views, defs)
    every = kast["theorem_values"] + kast["theorems"] + kast["definitions"] + \
            [dict(t, name="axiom " + t["name"]) for t in kast.get("axioms", [])]
    final = next(t for t in every if t["name"] == a.final)
    by_name = {t["name"]: t for t in every}
    flag = lambda k: next((f[1] for f in facts if f[0] == k), "false")

    def say(t):
        ants, cons = split_imp(t["conclusion"])
        body = "; ".join(r.render(c) for c in cons)
        return sentence(("if " + "; ".join(r.render(x) for x in ants) + ", then " + body) if ants else body)

    L = [f"Hidden premises of theorem {a.final} in {run.name}", ""]
    stated, _ = split_imp(final["conclusion"])
    L.append(f"Stated premises ({len(stated)}, for comparison):")
    L += ["  " + sentence(r.render(p)) for p in stated] or ["  none"]
    L.append("")
    axioms = res.get("kernel_report", {}).get("added_axioms") or []
    L.append("A. Axioms the source added: " + (", ".join(x.get("name", "?") for x in axioms) if axioms else "none"))
    L.append("")
    L.append("B. Definitions and axioms (each left out in turn; 'needed' means the theorem no longer follows without it;")
    L.append("   two items that can stand in for each other are each 'not needed' here, and section C keeps one of them):")
    if flag("baseline") != "true":
        L.append("  The generic proofs could not reproduce the theorem from all definitions, so B and C are not reliable.")
    for f in facts:
        if f[0] == "needed":
            L.append(f"  {f[1]}: " + ("needed" if f[2] == "true" else "not needed"))
            if f[2] == "true" and f[1] in by_name:
                L += ["      " + sentence(r.render(c)) for c in split_imp(by_name[f[1]]["conclusion"])[1]]
    L.append("")
    pieces = [f for f in facts if f[0] == "piece"]
    L.append(f"C. A smallest sufficient set of pieces ({len(pieces)}; every definition and axiom cut into pieces, every piece the proof can do without dropped):")
    for f in pieces:
        if f[1] in by_name:
            L.append(f"  {f[1]} (from {f[2]}): {say(by_name[f[1]])}")
    sets = [f[1].split(",") for f in facts if f[0] == "support_set"]
    done = any(f[0] == "supports_complete" and f[1] == "true" for f in facts)
    if len(sets) > 1 or not done:
        L.append(f"  Every smallest set ({len(sets)}" + (")" if done else "; the search stopped early, so there may be more)") + ":")
        L += [f"    set {k}: " + ", ".join(ns) for k, ns in enumerate(sets, 1)]
    alts = sorted({re.sub(r"#\d+.*$", "", f[1].removeprefix("axiom ")) for f in facts if f[0] == "alternative"})
    if alts:
        L.append("  In another smallest set but not in this one (they can stand in for items of this one): " + ", ".join(alts))
    checks = [f for f in facts if f[0] in ("set_suffices", "each_needed")]
    ok = bool(checks) and all(f[-1] == "true" for f in checks)
    L.append("  Rechecked by HOL4: " + ("the stated premises and these pieces give the theorem, and leaving out any one piece breaks it."
                                       if ok else "not confirmed: " + str([f for f in checks if f[-1] != "true"])))
    L.append("")
    declared = re.findall(r'new_constant\s*\(\s*"([^"]+)"', source)
    used = set()
    for t in [final] + [by_name[f[1]] for f in pieces if f[1] in by_name]:
        symbols(t["conclusion"], used)
    used_names = {s[1] for s in used}
    undefined = [c for c in declared if c in used_names]
    L.append(f"D. Undefined terms ({len(undefined)}): declared without a definition; HOL4 knows nothing about them but their name.")
    for c in undefined:
        g = notation.get(c, {}).get("gloss")
        L.append(f"  {c}: " + (g if g else "no comment"))
    L.append("")
    lists = lists_in(final["conclusion"], r.render)
    L.append("E. Closed lists (a written list is taken to be every argument that could defeat the term before it):")
    L += [f"  {h} {t} against {lst}." for h, t, lst in lists] or ["  none"]
    L.append("")
    L.append("F. Readings (HOL4 does not read comments; each symbol is taken to mean its comment):")
    seen = set()
    for kind, name, theory in sorted(used | {("constant", d.removesuffix("_def"), kast["theory"]) for d in def_names}, key=lambda s: s[1]):
        if theory not in (None, kast["theory"]) or name in seen or name.endswith("_fupd") or len(name) < 2 or kind == "variable":
            continue
        seen.add(name)
        g = notation.get(name, {}).get("gloss") or views.get(name, {}).get("gloss")
        L.append(f"  {name}: " + (g if g else "no comment; only its name says what it means"))
    L.append("")
    L.append("Not listed by this tool: any step from this theorem to a conclusion that is not written in HOL4.")
    (out / "hidden_premises.txt").write_text("\n".join(L) + "\n")
    (out / "hidden_premises.json").write_text(json.dumps({"facts": facts, "definitions": def_names}, indent=1))
    print("\n".join(L))


if __name__ == "__main__":
    main()
