open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s5p1";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);

val p5_1_01 = new_axiom ("p5_1_01", ``AcceptEach <=> (GoesBeyond /\ MakesSense ==> !a. Member a ==> Claim a)``);
val p5_1_02 = new_axiom ("p5_1_02", ``GoesBeyond /\ MakesSense /\ Member Ash``);

Theorem p5_1_03:
  AcceptEach ==> Claim Ash
Proof
  metis_tac [p5_1_01, p5_1_02]
QED


Theorem final:
  AcceptEach ==> Claim Ash
Proof
  metis_tac [p5_1_01, p5_1_02, p5_1_03]
QED

val _ = export_theory ();
