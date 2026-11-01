open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s4p1";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Rejects a : a rejects J *)
val _ = new_constant ("Rejects", ``:person -> bool``);
(* InGroup a : a belongs to the group of Williams's example *)
val _ = new_constant ("InGroup", ``:person -> bool``);
(* WilliamsQ10 : Williams writes that [Q10] *)
val _ = new_constant ("WilliamsQ10", ``:bool``);

val p4_1_01 = new_axiom ("p4_1_01", ``WilliamsQ10``);
val p4_1_02 = new_axiom ("p4_1_02", ``WilliamsQ10 ==> !a. InGroup a ==> Rejects a``);
val p4_1_03 = new_axiom ("p4_1_03", ``InGroup Ash /\ Member Ash /\ GoesBeyond /\ MakesSense``);

Theorem p4_1_04:
  Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense
Proof
  metis_tac [p4_1_01, p4_1_02, p4_1_03]
QED


Theorem final:
  Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense
Proof
  metis_tac [p4_1_01, p4_1_02, p4_1_03, p4_1_04]
QED

val _ = export_theory ();
