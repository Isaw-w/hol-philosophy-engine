open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s2p1";

(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* WouldSense : J would make sense to us as a legitimation of P as authority were we S in the light of C(S) *)
val _ = new_constant ("WouldSense", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Legit : realism counts P as legitimate over S as a whole *)
val _ = new_constant ("Legit", ``:bool``);
(* WilliamsLeg : Williams holds that what we acknowledge as legitimate here and now is what here and now makes sense as a legitimation of power as authority (2005, 11) *)
val _ = new_constant ("WilliamsLeg", ``:bool``);
(* WilliamsQ1 : Williams writes that [Q1] *)
val _ = new_constant ("WilliamsQ1", ``:bool``);
(* WilliamsQ2 : Williams writes that [Q2] *)
val _ = new_constant ("WilliamsQ2", ``:bool``);

val p2_1_01 = new_axiom ("p2_1_01", ``WilliamsQ1``);
val p2_1_02 = new_axiom ("p2_1_02", ``WilliamsLeg``);
val p2_1_03 = new_axiom ("p2_1_03", ``WilliamsQ2``);
val p2_1_04 = new_axiom ("p2_1_04", ``WilliamsLeg /\ WilliamsQ2 ==> (GoesBeyond /\ MakesSense ==> Legit)``);
val p2_1_05 = new_axiom ("p2_1_05", ``WilliamsQ1 /\ WilliamsQ2 ==> (MakesSense <=> GoesBeyond /\ WouldSense)``);

Theorem p2_1_06:
  (GoesBeyond /\ MakesSense ==> Legit) /\ (MakesSense <=> GoesBeyond /\ WouldSense)
Proof
  metis_tac [p2_1_01, p2_1_02, p2_1_03, p2_1_04, p2_1_05]
QED


Theorem final:
  (GoesBeyond /\ MakesSense ==> Legit) /\ (MakesSense <=> GoesBeyond /\ WouldSense)
Proof
  metis_tac [p2_1_01, p2_1_02, p2_1_03, p2_1_04, p2_1_05, p2_1_06]
QED

val _ = export_theory ();
