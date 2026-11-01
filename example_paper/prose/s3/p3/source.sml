open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s3p3";

val _ = new_type ("person", 0);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);
(* WilliamsQ9 : Williams writes that [Q9] *)
val _ = new_constant ("WilliamsQ9", ``:bool``);

val p3_3_01 = new_axiom ("p3_3_01", ``WR ==> (!a. Member a /\ Claim a ==> Reason a)``);
val p3_3_02 = new_axiom ("p3_3_02", ``WilliamsQ9``);
val p3_3_03 = new_axiom ("p3_3_03", ``WilliamsQ9 ==> (WR ==> (!a. Reason a ==> Corr a))``);

Theorem p3_3_04:
  WR ==> (!a. Member a /\ Claim a ==> Corr a)
Proof
  metis_tac [p3_3_01, p3_3_02, p3_3_03]
QED


Theorem final:
  WR ==> (!a. Member a /\ Claim a ==> Corr a)
Proof
  metis_tac [p3_3_01, p3_3_02, p3_3_03, p3_3_04]
QED

val _ = export_theory ();
