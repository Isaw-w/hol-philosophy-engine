"""Check the response's final conclusion against all of its own arguments. No model call; no change to the source.

  python3 tools/final_check.py runs/RUN                         # the theorem named final
  python3 tools/final_check.py runs/RUN --final other_name      # an earlier run without that name

Runs the unchanged source in HOL4 (with the optional deontic library on loadPath), then a fixed analysis script that
reads the theorems by the names the exporter found in kernel_ast.json. It reports facts only:
  - all premises: every distinct "if" part of every theorem (the considerations the response itself states)
  - which of them the final theorem does not use
  - whether the final theorem's conclusion is one of its own premises
  - conclusions of the other theorems that differ from the final one
  - for each such OughtNow X against the final OughtNow A: does HOL4 prove from all premises that X and A cannot both
    hold (then the response's own premises yield a dilemma its final theorem does not settle)
  - whether all premises together are contradictory
Writes <run>/final_check/final_check.json and final_check.txt.
"""
import argparse, json, re, shlex, subprocess
from pathlib import Path

ANALYSIS = r'''
local
  fun quote s = "\"" ^ String.translate (fn #"\"" => "\\\"" | #"\\" => "\\\\" | #"\n" => " " | c => str c) s ^ "\"";
  fun arr f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
  fun ts t = quote (Parse.term_to_string t);
  fun mem t ts = List.exists (fn u => aconv t u) ts;
  fun union xs = List.foldl (fn (t, acc) => if mem t acc then acc else acc @ [t]) [] xs;
  fun parts th =
    let val (_, body) = strip_forall (concl th)
    in if is_imp_only body then (strip_conj (fst (dest_imp_only body)), strip_conj (snd (dest_imp_only body)))   (* not ~P, which HOL4 also reads as P ==> F *)
       else ([], strip_conj body) end;
  fun oughtnow t =
    let val (f, args) = strip_comb t
    in if is_const f andalso #Name (dest_thy_const f) = "OughtNow" andalso length args = 2
       then SOME (hd args) else NONE end;
  (* the response's own definitions, and the deontic library's if the response loaded it (looked up by name) *)
  val defs = map snd (DB.definitions (current_theory ())) @ (map snd (DB.definitions "deontic") handle _ => [])
             @ List.mapPartial (fn n => SOME (DB.fetch "-" n) handle _ => NONE) SOURCE_DEFINITIONS;   (* pattern-matching ones are stored as theorems *)
  fun tryprove (asl, goal) =
    (TAC_PROOF ((asl, goal), rpt strip_tac >> fs defs >> PROVE_TAC []); true)
    handle _ => false;
  val (fants, fcons) = parts FINAL_THM;
  val allants = union (List.concat (map (fn (_, th) => fst (parts th)) NAMED));
  val unused = List.filter (fn t => not (mem t fants)) allants;
  (* an unused premise may still follow from the final theorem's premises and the response's definitions *)
  val implied = List.filter (fn t => tryprove (fants, t)) unused;
  val omitted = List.filter (fn t => not (mem t implied)) unused;
  val restates = List.exists (fn c => mem c fants) fcons;
  val competing = List.concat (map (fn (n, th) =>
      if n = FINAL_NAME then [] else
      map (fn c => (n, c)) (List.filter (fn c => not (mem c fcons)) (snd (parts th)))) NAMED);
  (* two plain statements: can they both hold, given all premises? *)
  fun plain (n, c) =
    if type_of c <> bool then NONE else
    let val pairs = List.mapPartial (fn fc =>
          if type_of fc <> bool orelse isSome (oughtnow fc) then NONE else
          let val goal = mk_neg (mk_conj (c, fc))
          in SOME ("{\"final_conclusion\":" ^ ts fc ^ ",\"goal\":" ^ ts goal ^
                   ",\"proved_from_all_premises\":" ^ Bool.toString (tryprove (allants, goal)) ^ "}") end
          handle e => SOME ("{\"final_conclusion\":" ^ ts fc ^ ",\"error\":" ^ quote (General.exnMessage e) ^ "}")) fcons
    in SOME ("{\"theorem\":" ^ quote n ^ ",\"conclusion\":" ^ ts c ^ ",\"exclusive_with_final\":" ^ arr (fn s => s) pairs ^ "}") end;
  fun exclusive (n, c) =
    case oughtnow c of
      NONE => plain (n, c)
    | SOME x =>
        let val pairs = List.mapPartial (fn fc =>
              case oughtnow fc of
                NONE => NONE
              | SOME a =>
                  let val ty = hd (fst (strip_fun (type_of a)))
                      val v = variant (free_varsl (allants @ [a, x])) (mk_var ("v", ty))
                      val goal = mk_forall (v, mk_neg (mk_conj (beta_conv (mk_comb (x, v)) handle _ => mk_comb (x, v),
                                                                beta_conv (mk_comb (a, v)) handle _ => mk_comb (a, v))))
                  in SOME ("{\"final_conclusion\":" ^ ts fc ^ ",\"goal\":" ^ ts goal ^
                           ",\"proved_from_all_premises\":" ^ Bool.toString (tryprove (allants, goal)) ^ "}") end
                  handle e => SOME ("{\"final_conclusion\":" ^ ts fc ^ ",\"error\":" ^ quote (General.exnMessage e) ^ "}")) fcons
        in SOME ("{\"theorem\":" ^ quote n ^ ",\"conclusion\":" ^ ts c ^ ",\"exclusive_with_final\":" ^ arr (fn s => s) pairs ^ "}") end;
  val contradictory = tryprove (allants, F);
  val excl = List.mapPartial exclusive competing;
in
  val out = TextIO.openOut "final_check.json";
  val _ = TextIO.output (out, "{\"final\":" ^ quote FINAL_NAME ^
    ",\"theorems\":" ^ arr (fn (n, _) => quote n) NAMED ^
    ",\"all_premises\":" ^ arr ts allants ^
    ",\"final_premises\":" ^ arr ts fants ^
    ",\"final_conclusions\":" ^ arr ts fcons ^
    ",\"unused_premises\":" ^ arr ts unused ^
    ",\"unused_but_implied\":" ^ arr ts implied ^
    ",\"unused_and_not_implied\":" ^ arr ts omitted ^
    ",\"final_restates_a_premise\":" ^ Bool.toString restates ^
    ",\"competing_conclusions\":" ^ arr (fn (n, c) => "{\"theorem\":" ^ quote n ^ ",\"conclusion\":" ^ ts c ^ "}") competing ^
    ",\"exclusivity\":" ^ arr (fn s => s) excl ^
    ",\"all_premises_contradictory\":" ^ Bool.toString contradictory ^ "}");
  val _ = TextIO.closeOut out;
end;
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run")
    ap.add_argument("--final", default="final")
    ap.add_argument("--host", default="mini")
    ap.add_argument("--library", default="~/thick_training/hol4_lib")
    a = ap.parse_args()
    run = Path(a.run); nc = run / "native_check" if (run / "native_check").is_dir() else run    # a model run, or a standalone check
    ast = json.loads((nc / "kernel_ast.json").read_text())
    definitions = {d["name"] for d in ast.get("definitions", [])}      # definitions are concepts, not arguments
    names = []
    for kind in ("theorem_values",):          # theorems the source itself binds (not those HOL4 generates for datatypes)
        for t in ast.get(kind, []):
            if t["name"] not in names and t["name"] not in definitions and not t["name"].endswith("_def"):
                names.append(t["name"])
    ident = re.compile(r"^[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*$")   # SML identifiers the compiler already accepted
    names = [n for n in names if ident.match(n)]
    out = run / "final_check"; out.mkdir(exist_ok=True)
    if a.final not in names:
        result = {"status": "no_final_theorem", "final": a.final, "theorems": names}
        (out / "final_check.json").write_text(json.dumps(result, indent=1))
        print(json.dumps(result)); return
    source_defs = re.findall(r"^Definition\s+([A-Za-z_][\w']*)(?:\[[^\]]*\])?\s*:", (nc / "source.sml").read_text(), re.M)
    analysis = (f'val SOURCE_DEFINITIONS = [{", ".join(json.dumps(n) for n in source_defs)}];\n'
                f'val NAMED = [{", ".join(f"({json.dumps(n)}, {n})" for n in names)}];\n'
                f'val FINAL_NAME = {json.dumps(a.final)};\nval FINAL_THM = {a.final};\n' + ANALYSIS)
    (out / "final_check.sml").write_text(analysis)
    (out / "source.sml").write_bytes((nc / "source.sml").read_bytes())
    driver = ('val _ = loadPath := "LIB" :: !loadPath;\n'
              'val _ = ((use "source.sml"; use "final_check.sml"; OS.Process.exit OS.Process.success)\n'
              '  handle e => (TextIO.output (TextIO.stdErr, General.exnMessage e ^ "\\n"); OS.Process.exit OS.Process.failure));\n')
    (out / "driver.sml").write_text(driver)
    remote = f"thick_training/final_check/{run.name}"
    subprocess.run(["ssh", a.host, f"rm -rf {shlex.quote(remote)} && mkdir -p {shlex.quote(remote)}"], check=True)
    subprocess.run(["scp", "-q", str(out / "final_check.sml"), str(out / "source.sml"), str(out / "driver.sml"), f"{a.host}:{remote}/"], check=True)
    cmd = (f"cd {shlex.quote(remote)} && sed -i '' \"s|LIB|$HOME/thick_training/hol4_lib|\" driver.sml && "
           f"HOL_NOCONFIG=1 ~/thick_training/tools/HOL4-trindemossen-2/bin/hol --noconfig < driver.sml > final_check.log 2>&1; echo exit $?")
    r = subprocess.run(["ssh", a.host, cmd], capture_output=True, text=True, timeout=900)
    subprocess.run(["scp", "-q", f"{a.host}:{remote}/final_check.log", str(out)], check=False)
    got = subprocess.run(["scp", "-q", f"{a.host}:{remote}/final_check.json", str(out)], check=False).returncode == 0
    if not got:
        result = {"status": "analysis_failed", "exit": r.stdout.strip(), "log_tail": (out / "final_check.log").read_text()[-1500:]}
        (out / "final_check.json").write_text(json.dumps(result, indent=1)); print(json.dumps(result, indent=1)); return
    res = json.loads((out / "final_check.json").read_text()); res["status"] = "analysed"
    (out / "final_check.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    L = [f"Final theorem: {res['final']}",
         f"It uses {len(res['final_premises'])} of the {len(res['all_premises'])} distinct premises stated anywhere in the response."]
    if res["unused_but_implied"]:
        L += ["Premises of other theorems that the final theorem does not state but derives from its own premises and the definitions:"] + ["  " + p for p in res["unused_but_implied"]]
    if res["unused_and_not_implied"]:
        L += ["Premises of other theorems that the final theorem neither uses nor implies:"] + ["  " + p for p in res["unused_and_not_implied"]]
    if res["final_restates_a_premise"]: L.append("Its conclusion is one of its own premises.")
    if res["competing_conclusions"]:
        L.append("Other conclusions the response derives:")
        L += [f"  {c['theorem']}: {c['conclusion']}" for c in res["competing_conclusions"]]
    for e in res["exclusivity"]:
        ps = e["exclusive_with_final"]
        clash = [p["final_conclusion"] for p in ps if p.get("proved_from_all_premises")]
        if any("error" in p for p in ps):
            L.append(f"  {e['theorem']} ({e['conclusion']}): not fully checked")
        if clash:
            L.append(f"  {e['theorem']} ({e['conclusion']}): the response's premises say it cannot hold together with " + "; ".join(clash))
        elif ps:
            L.append(f"  {e['theorem']} ({e['conclusion']}): nothing in the response's premises says it excludes any final conclusion")
    L.append("All premises together: " + ("contradictory" if res["all_premises_contradictory"] else "no contradiction found"))
    (out / "final_check.txt").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
