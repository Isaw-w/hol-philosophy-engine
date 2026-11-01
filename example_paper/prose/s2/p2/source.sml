open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s2p2";

(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* WouldSense : J would make sense to us as a legitimation of P as authority were we S in the light of C(S) *)
val _ = new_constant ("WouldSense", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Legit : realism counts P as legitimate over S as a whole *)
val _ = new_constant ("Legit", ``:bool``);
(* Many : a substantial number of S are satisfied *)
val _ = new_constant ("Many", ``:bool``);
(* RequiresAll : universal acceptance is required for meeting the demand *)
val _ = new_constant ("RequiresAll", ``:bool``);
(* Meets : P meets the demand for legitimation *)
val _ = new_constant ("Meets", ``:bool``);
(* WilliamsMeetsLeg : Williams holds that meeting the demand is what distinguishes a legitimate state from an illegitimate one (2005, 4) *)
val _ = new_constant ("WilliamsMeetsLeg", ``:bool``);
(* WilliamsQ3 : Williams writes that [Q3] *)
val _ = new_constant ("WilliamsQ3", ``:bool``);
(* WilliamsQ4 : Williams writes that [Q4] *)
val _ = new_constant ("WilliamsQ4", ``:bool``);

val p2_2_01 = new_axiom ("p2_2_01", ``MakesSense <=> GoesBeyond /\ WouldSense``);
val p2_2_02 = new_axiom ("p2_2_02", ``WilliamsQ3``);
val p2_2_03 = new_axiom ("p2_2_03", ``WilliamsQ3 ==> ~RequiresAll``);
val p2_2_04 = new_axiom ("p2_2_04", ``GoesBeyond /\ MakesSense ==> Legit``);
val p2_2_05 = new_axiom ("p2_2_05", ``WilliamsMeetsLeg``);
val p2_2_06 = new_axiom ("p2_2_06", ``WilliamsMeetsLeg ==> (Legit ==> Meets)``);
val p2_2_07 = new_axiom ("p2_2_07", ``WilliamsQ4``);
val p2_2_08 = new_axiom ("p2_2_08", ``WilliamsQ4 ==> (Meets ==> Many)``);

Theorem p2_2_09:
  (MakesSense <=> GoesBeyond /\ WouldSense) /\ ~RequiresAll /\ (MakesSense ==> Many)
Proof
  metis_tac [p2_2_01, p2_2_02, p2_2_03, p2_2_04, p2_2_05, p2_2_06, p2_2_07, p2_2_08]
QED


Theorem final:
  (MakesSense <=> GoesBeyond /\ WouldSense) /\ ~RequiresAll /\ (MakesSense ==> Many)
Proof
  metis_tac [p2_2_01, p2_2_02, p2_2_03, p2_2_04, p2_2_05, p2_2_06, p2_2_07, p2_2_08, p2_2_09]
QED

val _ = export_theory ();
