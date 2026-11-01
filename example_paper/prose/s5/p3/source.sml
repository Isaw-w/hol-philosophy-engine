open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s5p3";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* ExtToward a : externalism about authority holds toward a *)
val _ = new_constant ("ExtToward", ``:person -> bool``);

val p5_3_01 = new_axiom ("p5_3_01", ``AcceptEach ==> Claim Ash``);
val p5_3_02 = new_axiom ("p5_3_02", ``~Corr Ash``);
val p5_3_03 = new_axiom ("p5_3_03", ``!a. ExtToward a <=> Claim a /\ ~Corr a``);

Theorem p5_3_04:
  AcceptEach ==> ExtToward Ash
Proof
  metis_tac [p5_3_01, p5_3_02, p5_3_03]
QED


Theorem final:
  AcceptEach ==> ExtToward Ash
Proof
  metis_tac [p5_3_01, p5_3_02, p5_3_03, p5_3_04]
QED

val _ = export_theory ();
