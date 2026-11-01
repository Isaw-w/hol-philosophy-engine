open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s4p2";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* Rejects a : a rejects J *)
val _ = new_constant ("Rejects", ``:person -> bool``);
(* Hard a : a is a hard-case dissenter *)
val _ = new_constant ("Hard", ``:person -> bool``);
(* HardCasesExist : hard cases exist *)
val _ = new_constant ("HardCasesExist", ``:bool``);
(* WilliamsQ11 : Williams writes that [Q11] *)
val _ = new_constant ("WilliamsQ11", ``:bool``);

val p4_2_01 = new_axiom ("p4_2_01", ``Rejects Ash``);
val p4_2_02 = new_axiom ("p4_2_02", ``~Corr Ash``);
val p4_2_03 = new_axiom ("p4_2_03", ``!a. Hard a <=> Rejects a /\ ~Corr a``);

Theorem p4_2_04:
  Hard Ash
Proof
  metis_tac [p4_2_01, p4_2_02, p4_2_03]
QED

val p4_2_05 = new_axiom ("p4_2_05", ``WilliamsQ11``);
val p4_2_06 = new_axiom ("p4_2_06", ``WilliamsQ11 ==> HardCasesExist``);

Theorem p4_2_07:
  HardCasesExist
Proof
  metis_tac [p4_2_01, p4_2_02, p4_2_03, p4_2_04, p4_2_05, p4_2_06]
QED


Theorem p4_2_08:
  Hard Ash /\ HardCasesExist
Proof
  metis_tac [p4_2_01, p4_2_02, p4_2_03, p4_2_04, p4_2_05, p4_2_06, p4_2_07]
QED


Theorem final:
  Hard Ash /\ HardCasesExist
Proof
  metis_tac [p4_2_01, p4_2_02, p4_2_03, p4_2_04, p4_2_05, p4_2_06, p4_2_07, p4_2_08]
QED

val _ = export_theory ();
