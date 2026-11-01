open HolKernel Parse boolLib bossLib;
val _ = new_theory "valid_modus_ponens";

(* Expected verdict: an argument. Two premises, both needed, consistent, and they prove the conclusion. *)

val _ = new_type ("person", 0);
(* Socrates : Socrates *)
val _ = new_constant ("Socrates", ``:person``);
(* Human x : x is a human being *)
val _ = new_constant ("Human", ``:person -> bool``);
(* Mortal x : x is mortal *)
val _ = new_constant ("Mortal", ``:person -> bool``);

val all_humans_mortal = new_axiom ("all_humans_mortal", ``!x. Human x ==> Mortal x``);
val socrates_human = new_axiom ("socrates_human", ``Human Socrates``);

Theorem final:
  Mortal Socrates
Proof
  metis_tac [all_humans_mortal, socrates_human]
QED

val _ = export_theory ();
