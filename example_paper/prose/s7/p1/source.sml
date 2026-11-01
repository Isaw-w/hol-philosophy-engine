open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p1";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Legit : realism counts P as legitimate over S as a whole *)
val _ = new_constant ("Legit", ``:bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* PathA : the first path, keeping the two levels apart, is taken *)
val _ = new_constant ("PathA", ``:bool``);
(* FootholdA : Williams's texts give the first path a foothold *)
val _ = new_constant ("FootholdA", ``:bool``);
(* WilliamsCease : Williams says that those beyond blame's mechanisms are people we cease to blame (1995, 43) *)
val _ = new_constant ("WilliamsCease", ``:bool``);
(* SleatPol : Sleat reads Williams's politics as a relationship in which the state has the legitimate authority to coerce, wherever the demand has been met (2013, 123) *)
val _ = new_constant ("SleatPol", ``:bool``);
(* CostA : on the first path a legitimate state stands to some of its members in relationships that are not political in Sleat's sense *)
val _ = new_constant ("CostA", ``:bool``);
(* WilliamsQ13 : Williams writes that [Q13] *)
val _ = new_constant ("WilliamsQ13", ``:bool``);

val p7_1_01 = new_axiom ("p7_1_01", ``PathA ==> ~AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a)``);
val p7_1_02 = new_axiom ("p7_1_02", ``GoesBeyond /\ MakesSense ==> Legit``);
val p7_1_03 = new_axiom ("p7_1_03", ``GoesBeyond /\ MakesSense /\ Member Ash /\ ~Corr Ash``);

Theorem p7_1_04:
  PathA ==> ~AcceptEach /\ Legit /\ ~Claim Ash
Proof
  metis_tac [p7_1_01, p7_1_02, p7_1_03]
QED

val p7_1_05 = new_axiom ("p7_1_05", ``WilliamsQ13``);
val p7_1_06 = new_axiom ("p7_1_06", ``WilliamsCease``);
val p7_1_07 = new_axiom ("p7_1_07", ``WilliamsQ13 /\ WilliamsCease ==> FootholdA``);
val p7_1_08 = new_axiom ("p7_1_08", ``SleatPol``);
val p7_1_09 = new_axiom ("p7_1_09", ``SleatPol ==> CostA``);

Theorem p7_1_10:
  (PathA ==> ~AcceptEach /\ Legit /\ ~Claim Ash) /\ FootholdA /\ CostA
Proof
  metis_tac [p7_1_01, p7_1_02, p7_1_03, p7_1_04, p7_1_05, p7_1_06, p7_1_07, p7_1_08, p7_1_09]
QED


Theorem final:
  (PathA ==> ~AcceptEach /\ Legit /\ ~Claim Ash) /\ FootholdA /\ CostA
Proof
  metis_tac [p7_1_01, p7_1_02, p7_1_03, p7_1_04, p7_1_05, p7_1_06, p7_1_07, p7_1_08, p7_1_09, p7_1_10]
QED

val _ = export_theory ();
