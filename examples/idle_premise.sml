open HolKernel Parse boolLib bossLib;
val _ = new_theory "idle_premise";

(* Expected verdict: not an argument. HOL4 proves the conclusion, but the premise about Greece does no work,
   so the premises are not minimal. *)

val _ = new_type ("person", 0);
(* Socrates : Socrates *)
val _ = new_constant ("Socrates", ``:person``);
(* Human x : x is a human being *)
val _ = new_constant ("Human", ``:person -> bool``);
(* Mortal x : x is mortal *)
val _ = new_constant ("Mortal", ``:person -> bool``);
(* Greek x : x lived in Greece *)
val _ = new_constant ("Greek", ``:person -> bool``);

val all_humans_mortal = new_axiom ("all_humans_mortal", ``!x. Human x ==> Mortal x``);
val socrates_human = new_axiom ("socrates_human", ``Human Socrates``);
val socrates_greek = new_axiom ("socrates_greek", ``Greek Socrates``);

Theorem final:
  Mortal Socrates
Proof
  metis_tac [all_humans_mortal, socrates_human, socrates_greek]
QED

val _ = export_theory ();
