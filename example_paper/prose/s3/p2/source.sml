open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s3p2";

val _ = new_type ("person", 0);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* ClaimMade a : P claims authority over a *)
val _ = new_constant ("ClaimMade", ``:person -> bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Blames a : P's claim over a is focused blame of a's resistance *)
val _ = new_constant ("Blames", ``:person -> bool``);
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);
(* WilliamsTie : Williams assumes a close connection between focused blame and the agent's reasons (1995, 41) and concludes that the proleptic mechanism is likely to prove essential to an account of focused blame (1995, 44) *)
val _ = new_constant ("WilliamsTie", ``:bool``);
(* WilliamsQ7 : Williams writes that [Q7] *)
val _ = new_constant ("WilliamsQ7", ``:bool``);
(* WilliamsQ8 : Williams writes that [Q8] *)
val _ = new_constant ("WilliamsQ8", ``:bool``);
(* WilliamsQ14 : Williams writes that [Q14] *)
val _ = new_constant ("WilliamsQ14", ``:bool``);

val p3_2_01 = new_axiom ("p3_2_01", ``!a. Member a ==> ClaimMade a``);
val p3_2_02 = new_axiom ("p3_2_02", ``WilliamsQ7``);
val p3_2_03 = new_axiom ("p3_2_03", ``WilliamsQ14``);
val p3_2_04 = new_axiom ("p3_2_04", ``WilliamsQ7 /\ WilliamsQ14 ==> !a. ClaimMade a ==> Blames a``);
val p3_2_05 = new_axiom ("p3_2_05", ``WilliamsQ8``);
val p3_2_06 = new_axiom ("p3_2_06", ``WilliamsTie``);
val p3_2_07 = new_axiom ("p3_2_07", ``WilliamsQ8 /\ WilliamsTie ==> (WR ==> !a. Blames a /\ Claim a ==> Reason a)``);

Theorem p3_2_08:
  WR ==> (!a. Member a /\ Claim a ==> Reason a)
Proof
  metis_tac [p3_2_01, p3_2_02, p3_2_03, p3_2_04, p3_2_05, p3_2_06, p3_2_07]
QED


Theorem final:
  WR ==> (!a. Member a /\ Claim a ==> Reason a)
Proof
  metis_tac [p3_2_01, p3_2_02, p3_2_03, p3_2_04, p3_2_05, p3_2_06, p3_2_07, p3_2_08]
QED

val _ = export_theory ();
