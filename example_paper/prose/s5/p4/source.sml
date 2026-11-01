open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s5p4";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Legit : realism counts P as legitimate over S as a whole *)
val _ = new_constant ("Legit", ``:bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);

val p5_4_01 = new_axiom ("p5_4_01", ``Member Ash``);
val p5_4_02 = new_axiom ("p5_4_02", ``~Corr Ash``);

Theorem p5_4_03:
  (!a. Member a /\ Claim a ==> Corr a) ==> ~Claim Ash
Proof
  metis_tac [p5_4_01, p5_4_02]
QED

val p5_4_04 = new_axiom ("p5_4_04", ``GoesBeyond /\ MakesSense ==> Legit``);
val p5_4_05 = new_axiom ("p5_4_05", ``GoesBeyond /\ MakesSense``);

Theorem p5_4_06:
  ((!a. Member a /\ Claim a ==> Corr a) ==> ~Claim Ash) /\ Legit
Proof
  metis_tac [p5_4_01, p5_4_02, p5_4_03, p5_4_04, p5_4_05]
QED


Theorem final:
  ((!a. Member a /\ Claim a ==> Corr a) ==> ~Claim Ash) /\ Legit
Proof
  metis_tac [p5_4_01, p5_4_02, p5_4_03, p5_4_04, p5_4_05, p5_4_06]
QED

val _ = export_theory ();
