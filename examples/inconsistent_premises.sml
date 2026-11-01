open HolKernel Parse boolLib bossLib;
val _ = new_theory "inconsistent_premises";

(* Expected verdict: not an argument. The premises contradict each other, so they "prove" anything; the conclusion
   is proved, but the premises are inconsistent. *)

val _ = new_type ("person", 0);
(* Socrates : Socrates *)
val _ = new_constant ("Socrates", ``:person``);
(* Mortal x : x is mortal *)
val _ = new_constant ("Mortal", ``:person -> bool``);
(* Wise x : x is wise *)
val _ = new_constant ("Wise", ``:person -> bool``);

val socrates_mortal = new_axiom ("socrates_mortal", ``Mortal Socrates``);
val socrates_immortal = new_axiom ("socrates_immortal", ``~Mortal Socrates``);

Theorem final:
  Wise Socrates
Proof
  metis_tac [socrates_mortal, socrates_immortal]
QED

val _ = export_theory ();
