open HolKernel Parse boolLib bossLib;
val _ = new_theory "does_not_follow";

(* Expected verdict: not an argument. Affirming the consequent: the conclusion does not follow, so HOL4 cannot
   prove it. *)

val _ = new_type ("person", 0);
(* Socrates : Socrates *)
val _ = new_constant ("Socrates", ``:person``);
(* Human x : x is a human being *)
val _ = new_constant ("Human", ``:person -> bool``);
(* Mortal x : x is mortal *)
val _ = new_constant ("Mortal", ``:person -> bool``);

val all_humans_mortal = new_axiom ("all_humans_mortal", ``!x. Human x ==> Mortal x``);
val socrates_mortal = new_axiom ("socrates_mortal", ``Mortal Socrates``);

Theorem final:
  Human Socrates
Proof
  metis_tac [all_humans_mortal, socrates_mortal]
QED

val _ = export_theory ();
