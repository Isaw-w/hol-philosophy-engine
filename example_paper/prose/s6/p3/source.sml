open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s6p3";

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
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);
(* WilliamsDecides : in the 1995 essay or the 2005 book, Williams says whether a legitimate state has authority over a member whose own outlook gives no reason of authority *)
val _ = new_constant ("WilliamsDecides", ``:bool``);
(* SleatQ17 : Sleat writes that [Q17] *)
val _ = new_constant ("SleatQ17", ``:bool``);

val p6_3_01 = new_axiom ("p6_3_01", ``WR ==> (!a. Member a /\ Claim a ==> Corr a)``);
val p6_3_02 = new_axiom ("p6_3_02", ``~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a))``);

Theorem p6_3_03:
  (WR ==> AcceptEach) ==> ~WR
Proof
  metis_tac [p6_3_01, p6_3_02]
QED

val p6_3_04 = new_axiom ("p6_3_04", ``GoesBeyond /\ MakesSense ==> Legit``);
val p6_3_05 = new_axiom ("p6_3_05", ``GoesBeyond /\ MakesSense /\ Member Ash /\ ~Corr Ash``);

Theorem p6_3_06:
  WR ==> Legit /\ ~Claim Ash
Proof
  metis_tac [p6_3_01, p6_3_02, p6_3_03, p6_3_04, p6_3_05]
QED

val p6_3_07 = new_axiom ("p6_3_07", ``~WilliamsDecides``);
val p6_3_08 = new_axiom ("p6_3_08", ``SleatQ17``);

Theorem p6_3_09:
  ((WR ==> AcceptEach) ==> ~WR) /\ (WR ==> Legit /\ ~Claim Ash) /\ ~WilliamsDecides /\ SleatQ17
Proof
  metis_tac [p6_3_01, p6_3_02, p6_3_03, p6_3_04, p6_3_05, p6_3_06, p6_3_07, p6_3_08]
QED


Theorem final:
  ((WR ==> AcceptEach) ==> ~WR) /\ (WR ==> Legit /\ ~Claim Ash) /\ ~WilliamsDecides /\ SleatQ17
Proof
  metis_tac [p6_3_01, p6_3_02, p6_3_03, p6_3_04, p6_3_05, p6_3_06, p6_3_07, p6_3_08, p6_3_09]
QED

val _ = export_theory ();
