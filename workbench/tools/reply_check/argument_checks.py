"""Five checks of a checked HOL4 argument, measured against its theorem final. No model call.

  python3 tools/reply_check/argument_checks.py runs/DATE/RUN          # writes RUN/argument_checks/

Every question is decided by HOL4. The source's definitions are unfolded, each remaining true-or-false statement is
treated as a letter, and HOL4's tautology checker and SAT solver decide the result (exact when the letters are
independent, as with undefined constants applied to different constructors; the report says when a letter still holds
a quantifier).

  1. Consistency: can all of final's premises be true together? (one way they can, if so). Also all premises stated
     anywhere in the source.
  2. Sensitivity: each premise in turn is made false. For each conclusion: does it still follow, does it become open,
     or does its opposite follow?
  3. Near restatements: a conclusion that is the "then" part of one premise, or that one premise gives on its own.
  4. Foundations: premises that no other theorem in the source argues for: facts, rules ("if ... then ..."), and bare
     claims that use an undefined predicate.
  5. Open questions: for every predicate on the source's own types and every constructor, whether final's premises
     settle it true, settle it false, or leave it open.
  6. Statements about truth values: HOL reads "Knows p", "Ought p", "Dominates p q" on p's truth value. Each such
     statement is also read as a claim of its own; what holds only in the first reading (a contradiction, a settled
     fact) comes from that, and a statement whose arguments are all settled cannot tell apart claims of equal value.
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent))
from gloss_claims import glosses, split_imp                  # noqa: E402
from plain_english import Plain, sentence                    # noqa: E402
from native_check import check                               # noqa: E402

ANALYSIS = r'''
val _ = (load "HolSatLib") handle _ => ();
val _ = let
  fun fetch n = DB.fetch "-" n
  val defs = map fetch DEF_NAMES
  val others = OTHER_THMS
  fun out s = TextIO.print ("CHECK|" ^ String.translate (fn #"\n" => " " | c => str c) s ^ "\n")
  (* unfold the definitions, then turn quantifiers over finite types into cases (prop.sml), then simplify again *)
  fun unfold t =
    let val u = rhs (concl (SIMP_CONV (srw_ss ()) defs t)) handle _ => t
        val e = expand_finite u
    in herbrand_instances (debool (rhs (concl (SIMP_CONV (srw_ss ()) defs e)) handle _ => e)) end   (* prop.sml *)
  (* letters: every statement that is not built from not, and, or, if, iff *)
  val table = ref ([] : (term * term) list)
  val quantified = ref false
  fun letter t =
    case List.find (fn (a, _) => aconv a t) (!table) of
      SOME (_, v) => v
    | NONE => let val v = mk_var ("letter_" ^ Int.toString (length (!table) + 1), bool)
              in (if is_forall t orelse is_exists t orelse (is_eq t andalso type_of (lhs t) <> bool)
                  then quantified := true else ());
                 table := (t, v) :: !table; v end
  fun abs t =
    if aconv t T orelse aconv t F then t
    else if is_neg t then mk_neg (abs (dest_neg t))
    else if is_conj t then let val (a, b) = dest_conj t in mk_conj (abs a, abs b) end
    else if is_disj t then let val (a, b) = dest_disj t in mk_disj (abs a, abs b) end
    else if is_imp_only t then let val (a, b) = dest_imp_only t in mk_imp (abs a, abs b) end
    else if is_eq t andalso type_of (lhs t) = bool then mk_eq (abs (lhs t), abs (rhs t))
    else letter t
  fun taut t = (tautLib.TAUT_PROVE t; true) handle _ => false
  fun conj ps = if null ps then T else list_mk_conj ps
  (* axioms are background assumptions; a quantifier over a type with finitely many plain constructors (or over
     bool) is replaced by one instance per value, so the axiom becomes letters too *)
  fun instances t =
    if is_forall t then
      let val (v, b) = dest_forall t
          val ty = type_of v
          val ctors = (TypeBase.constructors_of ty) handle _ => []
          val vals = if ty = bool then [T, F]
                     else if not (null ctors) andalso List.all (fn k => type_of k = ty) ctors then ctors else []
      in if null vals then [t] else List.concat (map (fn k => instances (subst [v |-> k] b)) vals) end
    else [t]
  val axs = DB.axioms (current_theory ())
  val ax_inst = [] : term list          (* the axioms are starting points below, next to final's premises *)
  fun entails ps c = taut (abs (unfold (mk_imp (conj (ax_inst @ ps), c))))
  fun consistent ps = not (taut (abs (unfold (mk_neg (conj (ax_inst @ ps))))))
  (* where the letter check cannot decide (quantifiers over open types, arithmetic), metis decides, at most 5 s each *)
  val _ = (metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ()
  fun metis_entails ps c =
    (TAC_PROOF (([], if null ps then c else mk_imp (conj ps, c)), rpt strip_tac >> metis_tac defs); true) handle _ => false
  fun metis_consistent ps = not (metis_entails ps F)
  val _ = out ("axioms|" ^ Int.toString (length axs) ^ "|" ^ Int.toString (length ax_inst))
  val _ = out ("axioms_consistent|" ^ Bool.toString (null axs orelse consistent (map (concl o #2) axs)))
  fun model ps =
    let val t = abs (unfold (mk_neg (conj (ax_inst @ ps))))
    in (HolSatLib.SAT_PROVE t; "none")
       handle HolSatLib.SAT_cex th => term_to_string (fst (dest_imp_only (concl th)) handle _ => concl th)
            | _ => "unavailable" end
  val (_, body) = strip_forall (concl FINAL_THM)
  val (ants_t, cons_t) = if is_imp_only body then dest_imp_only body else (T, body)
  val premises = if aconv ants_t T then [] else strip_conj ants_t
  val starts = map (fn t => ("premise", t)) premises @ map (fn (n, th) => ("axiom " ^ n, concl th)) axs
  val ants = map #2 starts
  val _ = List.app (fn (i, (k, _)) => out ("start|" ^ Int.toString i ^ "|" ^ k))
                   (ListPair.zip (List.tabulate (length starts, fn i => i + 1), starts))
  val cons = strip_conj cons_t
  fun idx xs = ListPair.zip (List.tabulate (length xs, fn i => i + 1), xs)
  val _ = out ("baseline|" ^ Bool.toString (entails ants cons_t))
  (* conclusions the letter check can reproduce; the others need arithmetic or other reasoning *)
  val covered = List.map (fn (j, c) => (j, entails ants c)) (idx cons)
  val by_metis = List.map (fn (j, c) => (j, not (#2 (List.nth (covered, j - 1))) andalso metis_entails ants c)) (idx cons)
  val _ = List.app (fn (j, ok) => out ("covered|" ^ Int.toString j ^ "|" ^ Bool.toString ok)) covered
  val _ = List.app (fn (j, ok) => if ok then out ("by_metis|" ^ Int.toString j) else ()) by_metis
  fun is_metis j = #2 (List.nth (by_metis, j - 1)) handle _ => false
  fun is_covered j = (#2 (List.nth (covered, j - 1)) handle _ => false) orelse is_metis j
  (* the decision used for conclusion j *)
  fun entails_j j ps c = if is_metis j then metis_entails ps c else entails ps c
  fun consistent_j j ps = if is_metis j then metis_consistent ps else consistent ps
  (* 1. consistency *)
  val _ = out ("consistent_final|" ^ Bool.toString (consistent ants))
  val _ = out ("model_final|" ^ model ants)
  fun premises_of th = let val (_, b) = strip_forall (concl th)
                       in if is_imp_only b then strip_conj (fst (dest_imp_only b)) else [] end
  val all_ants = List.foldl (fn (t, acc) => if List.exists (fn u => aconv u t) acc then acc else acc @ [t]) []
                   (ants @ List.concat (map (premises_of o #2) others))
  (* other theorems may assume the contrary of a premise of final: an alternative case, not a contradiction *)
  val _ = List.app (fn (n, th) =>
      List.app (fn q => if not (List.exists (fn p => aconv p q) ants) andalso not (consistent (q :: ants))
                        then out ("contrary|" ^ n ^ "|" ^ term_to_string q) else ()) (premises_of th)) others
  (* 2. sensitivity *)
  (* a fact or a claim is made false; a rule ("if ... then ...") is left out, since denying a rule would assert
     its "if" part and deny its "then" part at once *)
  val _ = List.app (fn (i, p) =>
      let val is_rule = is_imp_only (snd (strip_forall p)) orelse is_forall p
          val flipped = if is_rule then map #2 (List.filter (fn (k, _) => k <> i) (idx ants))
                        else List.map (fn (k, q) => if k = i then mk_neg q else q) (idx ants)
          val _ = out ("how|" ^ Int.toString i ^ "|" ^ (if is_rule then "left_out" else "made_false"))
      in List.app (fn (j, c) => if not (is_covered j) then () else
           out ("flip|" ^ Int.toString i ^ "|" ^ Int.toString j ^ "|" ^
                (if not (consistent_j j flipped) then "inconsistent" else if entails_j j flipped c then "still" else
                 if entails_j j flipped (mk_neg c) then "opposite" else "open"))) (idx cons) end) (idx ants)
  (* 3b. a conclusion that the axioms and definitions give with no premise at all *)
  val _ = List.app (fn (j, c) => out ("axioms_give|" ^ Int.toString j ^ "|" ^ Bool.toString (not (null axs) andalso entails [] c))) (idx cons)
  fun ax_then (j, c) = List.mapPartial (fn (n, th) =>
      if List.exists (fn t => (is_imp_only t andalso aconv (snd (dest_imp_only t)) c) orelse aconv t c) (instances (concl th))
      then SOME n else NONE) axs
  val _ = List.app (fn (j, c) => out ("axiom_then|" ^ Int.toString j ^ "|" ^ String.concatWith "," (ax_then (j, c)))) (idx cons)
  (* 3. near restatements *)
  fun smallest_j j c = List.foldl (fn ((k, q), keep) =>
      let val rest = List.filter (fn (m, _) => m <> k) keep in if entails_j j (map #2 rest) c then rest else keep end) (idx ants) (idx ants)
  val _ = List.app (fn (j, c) => if not (is_covered j) then () else
      let val sup = smallest_j j c
          val thenpart = List.filter (fn (k, q) => is_imp_only q andalso aconv (snd (dest_imp_only q)) c) (idx ants)
      in out ("support|" ^ Int.toString j ^ "|" ^ String.concatWith "," (map (Int.toString o #1) sup) ^ "|" ^
              String.concatWith "," (map (Int.toString o #1) thenpart)) end) (idx cons)
  (* 4. foundations: is a premise a conclusion of some other theorem? *)
  fun concls_of th = let val (_, b) = strip_forall (concl th)
                     in strip_conj (if is_imp_only b then snd (dest_imp_only b) else b) end
  val _ = List.app (fn (i, p) =>
      (* a theorem argues for p only if p is one of its conclusions and not one of its own premises *)
      let val givers = List.filter (fn (n, th) => List.exists (fn c => aconv c p) (concls_of th)
                                                andalso not (List.exists (fn q => aconv q p) (premises_of th))) others
      in out ("argued|" ^ Int.toString i ^ "|" ^ String.concatWith "," (map #1 givers)) end) (idx ants)
  (* 5. open questions: predicates on this theory's own types, applied to each constructor *)
  val thy = current_theory ()
  val preds = List.filter (fn c =>
      let val (dom, rng) = dom_rng (type_of c)
      in rng = bool andalso (#Thy (dest_thy_type dom) = thy handle _ => false) end handle _ => false) (constants thy)
  val _ = List.app (fn pr =>
      let val dom = fst (dom_rng (type_of pr))
          val ctors = TypeBase.constructors_of dom handle _ => []
      in List.app (fn k =>
           if is_const k andalso type_of k = dom then
             let val t = mk_comb (pr, k)
             in out ("status|" ^ fst (dest_const pr) ^ "|" ^ fst (dest_const k) ^ "|" ^
                     (if entails ants t then "true" else if entails ants (mk_neg t) then "false" else "open")) end
           else ()) ctors end) preds
  (* 6. statements about truth values. HOL reads "Knows p", "Ought p", "Dominates p q" as functions of the truth
     value of p, while the argument may mean the claim p itself. Two readings are compared: on truth values (debool,
     as in every check above) and opaque (each such statement a letter of its own, whatever its argument) *)
  fun unfold_opaque t =
    let val u = rhs (concl (SIMP_CONV (srw_ss ()) defs t)) handle _ => t
        val e = expand_finite u
    in herbrand_instances (rhs (concl (SIMP_CONV (srw_ss ()) defs e)) handle _ => e) end
  fun opaque_entails ps c = taut (abs (unfold_opaque (mk_imp (conj (ax_inst @ ps), c))))
  fun opaque_consistent ps = not (taut (abs (unfold_opaque (mk_neg (conj (ax_inst @ ps))))))
  fun bool_args t = List.filter (fn a => type_of a = bool andalso not (aconv a T) andalso not (aconv a F)) (snd (strip_comb t))
  fun ops_in t acc =
    if aconv t T orelse aconv t F then acc
    else if is_neg t then ops_in (dest_neg t) acc
    else if is_conj t then let val (a, b) = dest_conj t in ops_in b (ops_in a acc) end
    else if is_disj t then let val (a, b) = dest_disj t in ops_in b (ops_in a acc) end
    else if is_imp_only t then let val (a, b) = dest_imp_only t in ops_in b (ops_in a acc) end
    else if is_eq t andalso type_of (lhs t) = bool then ops_in (rhs t) (ops_in (lhs t) acc)
    else if type_of t <> bool orelse is_forall t orelse is_exists t orelse is_abs t then acc
    else case bool_args t of
           [] => acc
         | bargs => List.foldl (fn (a, acc) => ops_in a acc) (if List.exists (fn u => aconv u t) acc then acc else acc @ [t]) bargs
  (* the rule: no predicate the source declares takes a truth value as an argument (decided by types alone) *)
  val _ = List.app (fn c =>
      let val (args, _) = strip_fun (type_of c)
      in if List.exists (fn ty => ty = bool) args
         then out ("tv_constant|" ^ fst (dest_const c) ^ "|" ^ type_to_string (type_of c)) else () end) (constants thy)
  val op_atoms = List.foldl (fn (p, acc) => ops_in (unfold_opaque p) acc) [] ants
  val ext_ok = consistent ants
  val _ = out ("tv_consistent|" ^ Bool.toString ext_ok ^ "|" ^ Bool.toString (opaque_consistent ants) ^ "|" ^ Int.toString (length op_atoms))
  fun settled a = if entails ants a then SOME T else if entails ants (mk_neg a) then SOME F else NONE
  val _ = if not ext_ok then () else List.app (fn t =>
      let val st = map (fn a => (a, settled a)) (bool_args t)
          val _ = List.app (fn (a, SOME v) =>
                      if opaque_entails ants (if aconv v T then a else mk_neg a) then ()
                      else out ("tv_forced|" ^ term_to_string a ^ "|" ^ term_to_string v ^ "|" ^ term_to_string t)
                    | _ => ()) st
          val (f, args) = strip_comb t
          fun value x = case List.find (fn (a, _) => aconv a x) st of SOME (_, SOME v) => v | _ => x
      in if List.all (fn (_, s) => isSome s) st
         then out ("tv_reduces|" ^ term_to_string t ^ "|" ^ term_to_string (list_mk_comb (f, map value args))) else () end) op_atoms
  val _ = List.app (fn (t, v) => out ("letter|" ^ fst (dest_var v) ^ "|" ^ term_to_string t)) (!table)
  val _ = out ("quantified_letters|" ^ Bool.toString (!quantified))
in () end;
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run"); ap.add_argument("--final", default="final"); ap.add_argument("--host", default="mini")
    a = ap.parse_args()
    run = Path(a.run); nc = run / "native_check"
    source = (nc / "source.sml").read_text()
    ast = json.loads((nc / "kernel_ast.json").read_text())
    notation, views = glosses(source)
    def_names = re.findall(r"^Definition\s+([A-Za-z_][\w']*)(?:\[[^\]]*\])?\s*:", source, re.M)
    def_names += re.findall(r"^val\s+([A-Za-z_][\w']*)\s*=\s*(?:Define|xDefine|new_definition)\b", source, re.M)
    ident = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")
    axiom_names = {t["name"] for t in ast.get("axioms", [])}
    others = [t["name"] for t in ast["theorem_values"]
              if t["name"] != a.final and t["name"] not in def_names and not t["name"].endswith("_def")
              and t["name"] not in axiom_names and ident.match(t["name"])]
    analysis = (HERE / "prop.sml").read_text() + "\n" + (ANALYSIS.replace("DEF_NAMES", "[" + ", ".join(json.dumps(n) for n in def_names) + "]")
                .replace("OTHER_THMS", "[" + ", ".join(f"({json.dumps(n)}, {n})" for n in others) + "]")
                .replace("FINAL_THM", a.final))
    ends = list(re.finditer(r"val\s+_\s*=\s*export_theory\s*\(\s*\)\s*;", source))
    i = ends[-1].start() if ends else len(source)
    out = run / "argument_checks"; out.mkdir(exist_ok=True)
    combined = out / "source_with_analysis.sml"
    combined.write_text(source[:i] + analysis + "\n" + source[i:])
    res = check(combined, out / "hol4", "hol4", a.host, timeout=3600)
    if res.get("status") != "processed":
        raise SystemExit(f"HOL4 did not process the analysis: {res.get('status')}")
    facts = [l.split("|")[1:] for l in (out / "hol4" / "native.log").read_text().splitlines() if l.startswith("CHECK|")]
    kast = json.loads((out / "hol4" / "kernel_ast.json").read_text())
    defs = {d["name"]: d for d in kast["definitions"]}
    r = Plain(notation, views, defs)
    every = {t["name"]: t for t in kast["theorem_values"] + kast["theorems"] + kast["definitions"]}
    stated, cons = split_imp(every[a.final]["conclusion"])
    axioms_by_name = {t["name"]: t for t in kast.get("axioms", [])}
    ants, P = [], {}
    for f in facts:
        if f[0] == "start":
            i, kind = int(f[1]), f[2]
            node = stated[i - 1] if kind == "premise" else axioms_by_name[kind.split(" ", 1)[1]]["conclusion"]
            ants.append(node)
            P[i] = (sentence(r.render(node)) if kind == "premise" else f"[{kind}] " + sentence(r.render(node)))
    C = {j + 1: sentence(r.render(c)) for j, c in enumerate(cons)}
    get = lambda k: [f for f in facts if f[0] == k]
    one = lambda k: (get(k) or [[k, ""]])[0]
    letters = {f[1]: f[2] for f in get("letter")}

    def read(text):
        """a letter's statement in words: a constant, or a predicate applied to a constructor"""
        t = text.strip().strip("()")
        parts = t.split()
        if len(parts) == 1:
            g = notation.get(parts[0], {}).get("gloss")
            return g or parts[0].replace("_", " ")
        if len(parts) == 2 and parts[0] in notation:
            e = notation[parts[0]]
            arg = notation.get(parts[1], {}).get("gloss") or parts[1]
            return r.substitute(e, [{"kind": "constant", "name": parts[1], "theory": kast["theory"]}]) if e["params"] else e["gloss"]
        return t

    L = [f"Five checks of {run.name}, measured against theorem {a.final}", ""]
    metis_ones = {int(f[1]) for f in get("by_metis")}
    if metis_ones:
        L += ["Conclusions " + ", ".join(map(str, sorted(metis_ones))) + " are decided by metis (5 s per question) instead of the letter check;",
              "for them, 'open' can also mean metis ran out of time.", ""]
    uncovered = [int(f[1]) for f in get("covered") if f[2] != "true" and int(f[1]) not in metis_ones]
    if uncovered:
        L += ["Conclusions " + ", ".join(map(str, uncovered)) + " need arithmetic or other reasoning that the letter check does not do;",
              "they are left out of sections 2 and 5 (HOL4 itself proved them).", ""]
    if one("quantified_letters")[1] == "true":
        L += ["Some letters still contain a quantifier or an equation between things that are not truth values, so 'consistent' and 'open' below are approximate.", ""]

    L.append("1. Consistency")
    L.append(f"  final's stated premises and the axioms ({len(P)} starting points) together: " + ("can all be true" if one("consistent_final")[1] == "true" else "CANNOT all be true (contradictory)"))
    contrary = get("contrary")
    if contrary:
        L.append("  other theorems that assume the contrary of final's premises (alternative cases):")
        L += [f"    {f[1]}: {f[2]}" for f in contrary]
    m = one("model_final")[1]
    if m not in ("", "none", "unavailable"):
        L.append("  One way they are all true (HOL4's SAT solver); letters not listed can be either:")
        for lit in [x.strip() for x in re.split(r"/\\|∧", m)]:
            neg = lit.startswith("~") or lit.startswith("¬")
            name = lit.lstrip("~¬").strip()
            if name in letters:
                L.append(f"    {'false' if neg else 'true '}: {read(letters[name])}")
    L.append("")

    ax = one("axioms")
    if len(ax) > 1 and ax[1] not in ("", "0"):
        L.insert(len(L) - 1, f"  the source's {ax[1]} axioms are starting points, numbered after final's stated premises")
        L.insert(len(L) - 1, "  the axioms by themselves: " + ("can all be true" if one("axioms_consistent")[1] == "true" else "CANNOT all be true (contradictory)"))
    L.append("2. Sensitivity (each fact or claim made false in turn, each rule left out; what happens to each conclusion)")
    how = {int(f[1]): f[2] for f in get("how")}
    flips = {}
    for f in get("flip"):
        flips.setdefault(int(f[1]), {})[int(f[2])] = f[3]
    for i in P:
        row = flips.get(i, {})
        opp = [j for j, v in row.items() if v == "opposite"]
        opn = [j for j, v in row.items() if v == "open"]
        if any(v == "inconsistent" for v in row.values()):
            kind = "making it false contradicts the other premises"
        elif opp:
            kind = "decisive: the opposite of conclusion " + ", ".join(map(str, opp)) + " follows" + (
                "; conclusion " + ", ".join(map(str, opn)) + " becomes open" if opn else "")
        elif opn:
            kind = "needed: conclusion " + ", ".join(map(str, opn)) + " becomes open"
        else:
            kind = "no effect: every conclusion still follows"
        L.append(f"  {i} ({'left out' if how.get(i) == 'left_out' else 'made false'}): {kind}")
    L.append("")

    L.append("3. Near restatements")
    given = [int(f[1]) for f in get("axioms_give") if f[2] == "true"]
    if given:
        L.append("  conclusions the axioms and definitions give with no premise at all: " + ", ".join(map(str, given)))
    axthen = {int(f[1]): [x for x in f[2].split(",") if x] for f in get("axiom_then")}
    for j, ns in sorted(axthen.items()):
        if ns:
            L.append(f"  conclusion {j}: it is the 'then' part of axiom " + ", ".join(ns))
    for f in get("support"):
        j, sup, thenpart = int(f[1]), [int(x) for x in f[2].split(",") if x], [int(x) for x in f[3].split(",") if x]
        notes = []
        if thenpart:
            notes.append("it is the 'then' part of premise " + ", ".join(map(str, thenpart)))
        if not sup:
            notes.append("the axioms and definitions give it with no premise")
        elif len(sup) == 1:
            notes.append(f"premise {sup[0]} gives it on its own (with the axioms and definitions)")
        if notes:
            L.append(f"  conclusion {j}: " + "; ".join(notes) + f" (smallest support: {', '.join(map(str, sup)) or 'none'})")
    L.append("")

    L.append("4. Foundations (starting points no other theorem argues for)")
    argued = {int(f[1]): [x for x in f[2].split(",") if x] for f in get("argued")}
    preds = set()
    for f in get("status"):
        preds.add(f[1])
    groups = {"fact": [], "rule": [], "bare claim": []}
    for i, p in enumerate(ants, 1):
        if argued.get(i):
            continue
        from gloss_claims import strip_comb
        h, args = strip_comb(p)
        is_rule = h["kind"] == "constant" and h["name"] in ("==>", "!")
        node = args[0] if (h["kind"] == "constant" and h["name"] == "~" and args) else p
        hh, aa = strip_comb(node)
        uses_pred = hh["kind"] == "constant" and hh["name"].split(".")[-1] in preds
        groups["rule" if is_rule else "bare claim" if uses_pred else "fact"].append(i)
    for label, desc in (("fact", "facts (from the user's account)"), ("rule", "rules (if ... then ...)"),
                        ("bare claim", "bare claims about reasons or status, with no argument")):
        if groups[label]:
            L.append(f"  {desc}: " + ", ".join(map(str, groups[label])))
            for i in groups[label]:
                L.append(f"    {i}. {P[i]}")
    sup_by = [f"{i} (by {', '.join(v)})" for i, v in argued.items() if v]
    L.append("  argued for elsewhere: " + (", ".join(sup_by) if sup_by else "none"))
    L.append("")

    L.append("5. Open questions (does final's premise set settle each predicate for each act?)")
    table = {}
    for f in get("status"):
        table.setdefault(f[1], {})[f[2]] = f[3]
    if not table:
        L.append("  no predicates on the source's own types")
    for pr, row in sorted(table.items()):
        gloss = notation.get(pr, {}).get("gloss", pr)
        L.append(f"  {pr} ({gloss}):")
        for k in sorted(row):                 # only the constructors of this predicate's own type
            v = row[k]
            L.append(f"    {k:<20} {'settled true' if v == 'true' else 'settled false' if v == 'false' else 'open'}")
    L.append("")
    tv = one("tv_consistent")
    L.append("6. Statements about truth values (\"Knows p\", \"Ought p\", \"Dominates p q\" take p's truth value, not the claim p)")
    tvc = get("tv_constant")
    L.append("  Rule (decided by types): no declared predicate takes a truth value. " + ("Kept." if not tvc else "BROKEN by:"))
    for f in tvc:
        L.append(f"    {f[1]} : {f[2]}")
    if tv and tv[3] == "0":
        L.append("  none in the premises")
    elif tv:
        L.append(f"  {tv[3]} such statements in the premises. Every check above reads them on truth values, as HOL does.")
        if tv[1] == "false" and tv[2] == "true":
            L.append("  The premises contradict each other ONLY because these statements take truth values: read as claims")
            L.append("  of their own, they can all be true. So final follows from a contradiction.")
        elif tv[1] == "false":
            L.append("  The premises contradict each other in both readings.")
        forced = {}
        for f in get("tv_forced"):
            forced.setdefault((f[1], f[2]), []).append(f[3])
        if forced:
            L.append("  Settled only because these statements take truth values (read as claims of their own, open):")
            for (a, v), ts in forced.items():
                L.append(f"    {a} is {'true' if v == 'T' else 'false'}   (through {'; '.join(sorted(set(ts)))})")
        red = get("tv_reduces")
        if red:
            L.append("  Statements whose true-or-false arguments are all settled, so they cannot tell apart claims with the")
            L.append("  same truth value (any other claim with the same value could stand in):")
            for f in red:
                L.append(f"    {f[1]}   says only   {f[2]}")
    L.append("")
    L.append("Starting points, numbered (final's stated premises first, then the axioms):")
    L += [f"  {i}. {P[i]}" for i in P]
    L.append("Conclusions of final, numbered:")
    L += [f"  {j}. {C[j]}" for j in C]
    (out / "argument_checks.txt").write_text("\n".join(L) + "\n")
    (out / "argument_checks.json").write_text(json.dumps({"facts": facts}, indent=1))
    print("\n".join(L))


if __name__ == "__main__":
    main()
