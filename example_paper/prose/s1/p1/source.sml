open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s1p1";

val _ = new_type ("person", 0);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Legit : realism counts P as legitimate over S as a whole *)
val _ = new_constant ("Legit", ``:bool``);
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);

val p1_1_01 = new_axiom ("p1_1_01", ``GoesBeyond /\ MakesSense ==> Legit``);
val p1_1_02 = new_axiom ("p1_1_02", ``WR ==> (!a. Reason a ==> Corr a)``);

Theorem p1_1_03:
  (GoesBeyond /\ MakesSense ==> Legit) /\ (WR ==> (!a. Reason a ==> Corr a))
Proof
  metis_tac [p1_1_01, p1_1_02]
QED


Theorem final:
  (GoesBeyond /\ MakesSense ==> Legit) /\ (WR ==> (!a. Reason a ==> Corr a))
Proof
  metis_tac [p1_1_01, p1_1_02, p1_1_03]
QED

val _ = export_theory ();
