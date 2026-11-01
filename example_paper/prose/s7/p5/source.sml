open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p5";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* PathE : the fifth path, cutting the link between authority and reasons, is taken *)
val _ = new_constant ("PathE", ``:bool``);
(* WilliamsJustified : Williams allows that what presents itself as blame may in fact be only a rejection of what someone has done, perhaps an entirely justified one (1995, 44) *)
val _ = new_constant ("WilliamsJustified", ``:bool``);
(* WilliamsWarfare : Williams separates the reasons given by a claim for authority from the reasons for stopping warfare (2005, 6) *)
val _ = new_constant ("WilliamsWarfare", ``:bool``);
(* CostE : the fifth path goes against Williams's account of the reasons a claim of authority gives *)
val _ = new_constant ("CostE", ``:bool``);

val p7_5_01 = new_axiom ("p7_5_01", ``PathE ==> AcceptEach /\ (!a. Reason a ==> Corr a)``);
val p7_5_02 = new_axiom ("p7_5_02", ``AcceptEach ==> Claim Ash``);
val p7_5_03 = new_axiom ("p7_5_03", ``~Corr Ash``);

Theorem p7_5_04:
  PathE ==> Claim Ash /\ ~Reason Ash
Proof
  metis_tac [p7_5_01, p7_5_02, p7_5_03]
QED

val p7_5_05 = new_axiom ("p7_5_05", ``WilliamsJustified``);
val p7_5_06 = new_axiom ("p7_5_06", ``WilliamsWarfare``);
val p7_5_07 = new_axiom ("p7_5_07", ``WilliamsWarfare ==> CostE``);

Theorem p7_5_08:
  (PathE ==> Claim Ash /\ ~Reason Ash) /\ WilliamsJustified /\ CostE
Proof
  metis_tac [p7_5_01, p7_5_02, p7_5_03, p7_5_04, p7_5_05, p7_5_06, p7_5_07]
QED


Theorem final:
  (PathE ==> Claim Ash /\ ~Reason Ash) /\ WilliamsJustified /\ CostE
Proof
  metis_tac [p7_5_01, p7_5_02, p7_5_03, p7_5_04, p7_5_05, p7_5_06, p7_5_07, p7_5_08]
QED

val _ = export_theory ();
