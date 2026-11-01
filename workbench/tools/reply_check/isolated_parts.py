"""Find every part of a checked HOL4 argument that the final theorem does not use. No model call.

  python3 tools/reply_check/isolated_parts.py runs/DATE/RUN          # writes RUN/isolated_parts/

"Isolated" is measured against the theorem named final, with HOL4 deciding each question:

  1. Unused definitions: the theorem still follows when the definition is left out.
  2. Other theorems outside its reach: a conclusion of another theorem that final's own premises do not give.
  3. Unused symbols and acts: declared constants, type constructors and defined terms that appear neither in final
     nor in a definition final needs.
  4. Idle premises of final: premises it can do without. HOL4 finds a smallest set of final's premises that still
     gives every conclusion; the rest are idle. (A smallest set: no premise in it can be left out. Another set may
     also work.)
  5. Separate parts inside final: for each conclusion, a smallest set of final's premises that gives it. Conclusions
     whose sets share no premise are separate arguments placed side by side.
  6. Support structure: every smallest set of every conclusion (prop.sml, all_smallest), read as linked, convergent,
     serial and divergent support. Conductive support is not decided: it needs to know which reasons count for and which
     against, which is meaning, not logic.
"""
import argparse, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent))
from gloss_claims import glosses, split_imp                  # noqa: E402
from plain_english import Plain, sentence                    # noqa: E402
from native_check import check                               # noqa: E402
from hidden_premises import symbols                          # noqa: E402

ANALYSIS = r'''
val _ = let
  fun fetch n = DB.fetch "-" n
  val def_names = DEF_NAMES
  val axs = DB.axioms (current_theory ())
  val defs = map fetch def_names @ map #2 axs
  val others = OTHER_THMS
  val extra = [DISJ_IMP_THM, FORALL_AND_THM]
  val _ = (metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ()
  fun out s = TextIO.print ("ISOLATED|" ^ String.translate (fn #"\n" => " " | c => str c) s ^ "\n")
  fun by_rw ths g = (TAC_PROOF (([], g), rw (ths @ extra) >> rpt (FIRST [decide_tac, metis_tac ths])); true) handle _ => false
  fun by_metis ths g = (TAC_PROOF (([], g), rpt strip_tac >> metis_tac ths); true) handle _ => false
  fun follows ths g = follows_each [] ths g
  val (_, body) = strip_forall (concl FINAL_THM)
  val (ants_t, cons_t) = if is_imp_only body then dest_imp_only body else (T, body)
  val ants = if aconv ants_t T then [] else strip_conj ants_t
  val cons = strip_conj cons_t
  (* the argument's starting points: final's stated premises and the source's axioms, numbered together *)
  val starts = map (fn t => ("premise", t)) ants @ map (fn (n, th) => ("axiom " ^ n, concl th)) axs
  val numbered = ListPair.zip (List.tabulate (length starts, fn i => i + 1), map #2 starts)
  val _ = List.app (fn (i, (k, _)) => out ("start|" ^ Int.toString i ^ "|" ^ k))
                   (ListPair.zip (List.tabulate (length starts, fn i => i + 1), starts))
  val def_ths = map fetch def_names
  fun gives ps c = follows def_ths (if null ps then c else mk_imp (list_mk_conj (map #2 ps), c))
  val _ = out ("baseline|" ^ Bool.toString (gives numbered cons_t))
  (* 1. definitions the theorem does without *)
  val _ = List.app (fn n =>
      out ("definition|" ^ n ^ "|" ^ Bool.toString (follows (map fetch (List.filter (fn m => m <> n) def_names) @ map #2 axs) (concl FINAL_THM))))
      def_names
  val _ = List.app (fn (n, _) =>
      out ("axiom|" ^ n ^ "|" ^ Bool.toString (follows (map fetch def_names @ map #2 (List.filter (fn (m, _) => m <> n) axs)) (concl FINAL_THM))))
      axs
  (* 2. conclusions of the other theorems: does final's own premise set give them? *)
  val _ = List.app (fn (n, th) =>
      let val (_, b) = strip_forall (concl th)
          val cs = strip_conj (if is_imp_only b then snd (dest_imp_only b) else b)
      in List.app (fn (j, c) => out ("theorem|" ^ n ^ "|" ^ Int.toString j ^ "|" ^ Bool.toString (gives numbered c)))
           (ListPair.zip (List.tabulate (length cs, fn j => j + 1), cs)) end) others
  (* 4 and 5. smallest premise sets *)
  fun smallest c = List.foldl (fn (p, keep) =>
      let val rest = List.filter (fn q => #1 q <> #1 p) keep in if gives rest c then rest else keep end) numbered numbered
  val core = smallest cons_t
  val _ = out ("core|" ^ String.concatWith "," (map (Int.toString o #1) core))
  (* every smallest set of starting points for each conclusion (prop.sml, all_smallest). A starting point is used
     when it is in one of them; it is isolated when it is in none *)
  fun term_of i = #2 (valOf (List.find (fn (k, _) => k = i) numbered))
  fun gives_ids ids c = gives (map (fn i => (i, term_of i)) ids) c
  val ids = map #1 numbered
  val numbered_cons = ListPair.zip (List.tabulate (length cons, fn j => j + 1), cons)
  val per = map (fn (j, c) => (j, c, all_smallest gives_ids ids c)) numbered_cons
  val _ = List.app (fn (j, _, (ss, done)) =>
      (out ("support|" ^ Int.toString j ^ "|" ^ String.concatWith "," (map Int.toString (if null ss then [] else List.last ss)));
       List.app (fn s => out ("supports|" ^ Int.toString j ^ "|" ^ String.concatWith "," (map Int.toString s))) ss;
       out ("complete|" ^ Int.toString j ^ "|" ^ Bool.toString done))) per
  fun in_some i = List.exists (fn (_, _, (ss, _)) => List.exists (fn s => List.exists (fn k => k = i) s) ss) per
  val _ = List.app (fn (i, _) =>
      if List.exists (fn (k, _) => k = i) core then () else out ("relevant|" ^ Int.toString i ^ "|" ^ Bool.toString (in_some i))) numbered
  (* serial: another theorem T is a step on the way to conclusion j when a smallest set of j contains a smallest set
     of T (and more), the rest of j's set together with T gives j, and T alone does not *)
  fun minus a b = List.filter (fn x => not (List.exists (fn y => y = x) b)) a
  fun subset a b = List.all (fn x => List.exists (fn y => y = x) b) a
  val _ = List.app (fn (n, th) =>
      let val (ts, _) = all_smallest gives_ids ids (concl th)
      in List.app (fn (j, c, (ss, _)) =>
           if gives [(0, concl th)] c then ()
           else if List.exists (fn s => List.exists (fn s1 => not (null s1) andalso subset s1 s andalso length s1 < length s
                      andalso gives ((0, concl th) :: map (fn i => (i, term_of i)) (minus s s1)) c) ts) ss
           then out ("serial|" ^ n ^ "|" ^ Int.toString j) else ()) per end) others
  (* the same test between final's own conclusions: conclusion j is a step on the way to conclusion k *)
  val _ = List.app (fn (j, cj, (sj, _)) => List.app (fn (k, ck, (sk, _)) =>
      if j = k orelse gives [(0, cj)] ck then ()
      else if List.exists (fn s => List.exists (fn s1 => not (null s1) andalso subset s1 s andalso length s1 < length s
                 andalso gives ((0, cj) :: map (fn i => (i, term_of i)) (minus s s1)) ck) sj) sk
      then out ("step|" ^ Int.toString j ^ "|" ^ Int.toString k) else ()) per) per
in () end;
'''


def datatype_constructors(source):
    found = []
    for m in re.finditer(r"Datatype\s*`([^`]*)`|Datatype:\s*(.*?)\nEnd", source, re.S):
        body = m.group(1) or m.group(2)
        for decl in re.split(r";", body):
            if "=" not in decl or "<|" in decl:
                continue
            rhs = decl.split("=", 1)[1]
            found += [alt.strip().split()[0] for alt in rhs.split("|") if alt.strip()]
    return found


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
    analysis = ((HERE / "prop.sml").read_text() + "\n" + ANALYSIS.replace("DEF_NAMES", "[" + ", ".join(json.dumps(n) for n in def_names) + "]")
                .replace("OTHER_THMS", "[" + ", ".join(f"({json.dumps(n)}, {n})" for n in others) + "]")
                .replace("FINAL_THM", a.final))
    ends = list(re.finditer(r"val\s+_\s*=\s*export_theory\s*\(\s*\)\s*;", source))
    i = ends[-1].start() if ends else len(source)
    out = run / "isolated_parts"; out.mkdir(exist_ok=True)
    combined = out / "source_with_analysis.sml"
    combined.write_text(source[:i] + analysis + "\n" + source[i:])
    res = check(combined, out / "hol4", "hol4", a.host, timeout=3600)
    if res.get("status") != "processed":
        raise SystemExit(f"HOL4 did not process the analysis: {res.get('status')}")
    facts = [l.split("|")[1:] for l in (out / "hol4" / "native.log").read_text().splitlines() if l.startswith("ISOLATED|")]
    kast = json.loads((out / "hol4" / "kernel_ast.json").read_text())
    defs = {d["name"]: d for d in kast["definitions"]}
    r = Plain(notation, views, defs)
    every = {t["name"]: t for t in kast["theorem_values"] + kast["theorems"] + kast["definitions"]}
    final = every[a.final]
    ants, cons = split_imp(final["conclusion"])
    axioms_by_name = {t["name"]: t for t in kast.get("axioms", [])}
    P = {}
    for f in facts:
        if f[0] == "start":
            i, kind = int(f[1]), f[2]
            if kind == "premise":
                P[i] = sentence(r.render(ants[i - 1]))
            else:
                name = kind.split(" ", 1)[1]
                P[i] = f"[axiom {name}] " + sentence(r.render(axioms_by_name[name]["conclusion"])) if name in axioms_by_name else f"[axiom {name}]"
    C = {j + 1: sentence(r.render(c)) for j, c in enumerate(cons)}
    get = lambda k: [f for f in facts if f[0] == k]
    nums = lambda s: [int(x) for x in s.split(",") if x]

    L = [f"Isolated parts of {run.name}, measured against theorem {a.final}", ""]
    if not get("baseline") or get("baseline")[0][1] != "true":
        L += ["The generic proofs could not reproduce the theorem from its premises and definitions; results below are not reliable.", ""]
    unused_defs = [f[1] for f in get("definition") if f[2] == "true"]
    L.append(f"1. Unused definitions ({len(unused_defs)}): the theorem still follows without them.")
    for n in unused_defs:
        g = notation.get(n.removesuffix("_def"), {}).get("gloss") or views.get(n.removesuffix("_def"), {}).get("gloss")
        L.append(f"  {n}" + (f": {g}" if g else ""))
    unused_axioms = [f[1] for f in get("axiom") if f[2] == "true"]
    if get("axiom"):
        L.append(f"1b. Unused axioms ({len(unused_axioms)} of {len(get('axiom'))}): " + (", ".join(unused_axioms) if unused_axioms else "none"))
    L.append("")
    outside = [f for f in get("theorem") if f[3] == "false"]
    L.append(f"2. Conclusions of other theorems that final's premises do not give ({len(outside)}):")
    for n, j, _ in [(f[1], int(f[2]), f[3]) for f in outside]:
        _, tc = split_imp(every[n]["conclusion"])
        L.append(f"  {n}: {sentence(r.render(tc[j - 1]))}")
    inside = sorted({f[1] for f in get("theorem")} - {f[1] for f in outside})
    L.append("  Other theorems whose every conclusion final's premises give: " + (", ".join(inside) if inside else "none"))
    L.append("")
    needed_defs = [f[1] for f in get("definition") if f[2] == "false"]
    used = set()
    symbols(final["conclusion"], used)
    for n in needed_defs:
        if n in every:
            symbols(every[n]["conclusion"], used)
    axioms_ast = {t["name"]: t for t in kast.get("axioms", [])}
    for f in get("axiom"):                        # an axiom final needs counts like a definition it needs
        if f[2] == "false" and f[1] in axioms_ast:
            symbols(axioms_ast[f[1]]["conclusion"], used)
    used = {s[1] for s in used}
    elsewhere = set()
    for n in others:
        symbols(every[n]["conclusion"], elsewhere)
    for t in axioms_ast.values():
        symbols(t["conclusion"], elsewhere)
    elsewhere = {s[1] for s in elsewhere}
    declared = re.findall(r'new_constant\s*\(\s*"([^"]+)"', source)
    constructors = datatype_constructors(source)
    defined = [n.removesuffix("_def") for n in def_names]
    L.append("3. Symbols and acts that appear neither in final nor in a definition or axiom it needs:")
    for label, group in (("declared constants", declared), ("type constructors (acts and the like)", constructors), ("defined terms", defined)):
        unused = [c for c in group if c not in used]
        if unused:
            L.append(f"  {label}: " + ", ".join(c + ("" if c in elsewhere else " (in no theorem at all)") for c in unused))
    L.append("")
    core = nums(get("core")[0][1]) if get("core") else list(P)
    idle = [i for i in P if i not in core]
    L.append(f"4. Idle starting points ({len(idle)} of {len(P)}; final's stated premises and the axioms): a smallest set that still gives every conclusion is "
             + ", ".join(map(str, core)) + "; the others are idle.")
    relevant = {int(f[1]): f[2] == "true" for f in get("relevant")}
    for i in idle:
        tag = " — in a smallest set of one of final's conclusions (convergent support, see 6)" if relevant.get(i) else ""
        L.append(f"  {i}: {P[i]}{tag}")
    if relevant:
        conv = [i for i in idle if relevant.get(i)]
        dead = [i for i in idle if not relevant.get(i)]
        L.append(f"  Of these, {len(conv)} are in a smallest set of some conclusion (they support it convergently);"
                 f" {len(dead)} are in none, so nothing final concludes uses them: " + (", ".join(map(str, dead)) if dead else "none") + ".")
        L.append("  (Every smallest set of every conclusion was found; see 6.)")
    L.append("")
    support = {int(f[1]): nums(f[2]) for f in get("support")}
    parent = {j: j for j in C}
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for j in C:
        for k in C:
            if j < k and set(support.get(j, [])) & set(support.get(k, [])):
                parent[find(k)] = find(j)
    groups = {}
    for j in C:
        groups.setdefault(find(j), []).append(j)
    L.append(f"5. Separate parts inside final ({len(groups)}): conclusions whose smallest supporting sets share no starting point.")
    for n, js in enumerate(groups.values(), 1):
        prem = sorted({i for j in js for i in support.get(j, [])})
        L.append(f"  Part {n}:")
        for j in js:
            L.append(f"    conclusion {j}: {C[j]}  [from {', '.join(map(str, support.get(j, []))) or 'definitions alone'}]")
        for i in prem:
            L.append(f"      {i}: {P[i]}")
    L.append("")
    short = {int(f[1]): (f[2].split(" ", 1)[1] if f[2].startswith("axiom ") else f"premise {f[1]}") for f in get("start")}
    sets = {}
    for f in get("supports"):
        sets.setdefault(int(f[1]), []).append(nums(f[2]))
    done = {int(f[1]): f[2] == "true" for f in get("complete")}
    via = {}
    for f in get("serial"):
        via.setdefault(int(f[2]), []).append(f[1])
    L.append("6. Support structure, read off every smallest set of every conclusion:")
    L.append("  linked = items needed together (one smallest set); convergent = two or more smallest sets;")
    L.append("  serial = goes through another theorem; divergent = one item supports two conclusions, neither a step to the other.")
    L.append("  Conductive support is not decided here: it needs to know which reasons count for and which against.")
    for j in C:
        ss = sets.get(j, [])
        L.append(f"  conclusion {j}: {C[j]}")
        if not ss:
            L.append("    does not follow from the starting points")
        kinds = []
        if len(ss) > 1:
            kinds.append(f"convergent ({len(ss)} smallest sets)")
        if any(len(x) > 1 for x in ss):
            kinds.append("linked")
        if via.get(j):
            kinds.append("serial, through " + ", ".join(via[j]))
        if kinds:
            L.append("    " + "; ".join(kinds))
        for x in ss:
            L.append("    {" + ", ".join(short.get(i, str(i)) for i in x) + "}" if x else "    {} (from definitions alone)")
        if not done.get(j, True):
            L.append("    (the search stopped early: there may be more smallest sets)")
    uses = {}
    for j, ss in sets.items():
        for i in {i for x in ss for i in x}:
            uses.setdefault(i, []).append(j)
    steps = {(int(f[1]), int(f[2])) for f in get("step")}
    for j, k in sorted(steps):
        L.append(f"  conclusion {j} is a step on the way to conclusion {k}")
    # divergent: one item supports two conclusions, neither of which is a step to the other
    div = {}
    for i, js in uses.items():
        pairs = [(a, b) for a in js for b in js if a < b and (a, b) not in steps and (b, a) not in steps]
        if pairs:
            div[i] = sorted({x for pr in pairs for x in pr})
    L.append("  divergent: " + ("; ".join(f"{short.get(i, i)} supports conclusions {', '.join(map(str, js))}" for i, js in sorted(div.items())) if div else "none"))
    L.append("")
    L.append("All starting points, numbered (final's stated premises first, then the axioms):")
    L += [f"  {i}. {P[i]}" for i in P]
    (out / "isolated_parts.txt").write_text("\n".join(L) + "\n")
    (out / "isolated_parts.json").write_text(json.dumps({"facts": facts}, indent=1))
    print("\n".join(L))


if __name__ == "__main__":
    main()
