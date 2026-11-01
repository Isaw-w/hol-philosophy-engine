open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s3p1";

val _ = new_type ("person", 0);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* Coercible a : P can rightfully coerce a by its own lights *)
val _ = new_constant ("Coercible", ``:person -> bool``);
(* ClaimMade a : P claims authority over a *)
val _ = new_constant ("ClaimMade", ``:person -> bool``);
(* WilliamsQ5 : Williams writes that [Q5] *)
val _ = new_constant ("WilliamsQ5", ``:bool``);
(* WilliamsQ6 : Williams writes that [Q6] *)
val _ = new_constant ("WilliamsQ6", ``:bool``);

val p3_1_01 = new_axiom ("p3_1_01", ``WilliamsQ5``);
val p3_1_02 = new_axiom ("p3_1_02", ``WilliamsQ5 ==> !a. Member a ==> Coercible a``);
val p3_1_03 = new_axiom ("p3_1_03", ``WilliamsQ6``);
val p3_1_04 = new_axiom ("p3_1_04", ``WilliamsQ6 ==> !a. Coercible a ==> ClaimMade a``);

Theorem p3_1_05:
  !a. Member a ==> ClaimMade a
Proof
  metis_tac [p3_1_01, p3_1_02, p3_1_03, p3_1_04]
QED


Theorem final:
  !a. Member a ==> ClaimMade a
Proof
  metis_tac [p3_1_01, p3_1_02, p3_1_03, p3_1_04, p3_1_05]
QED

val _ = export_theory ();
