open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s6p2";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* RequiresAll : universal acceptance is required for meeting the demand *)
val _ = new_constant ("RequiresAll", ``:bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);
(* PointsFirst : Williams's treatment of dissenters points to the strong reading, and Sleat reads Williams as holding it *)
val _ = new_constant ("PointsFirst", ``:bool``);
(* SupportsBoth : Williams's texts support both horns of the dilemma *)
val _ = new_constant ("SupportsBoth", ``:bool``);
(* WilliamsDecides : in the 1995 essay or the 2005 book, Williams says whether a legitimate state has authority over a member whose own outlook gives no reason of authority *)
val _ = new_constant ("WilliamsDecides", ``:bool``);
(* SleatQ12 : Sleat writes that [Q12] *)
val _ = new_constant ("SleatQ12", ``:bool``);
(* WilliamsQ15 : Williams writes that [Q15] *)
val _ = new_constant ("WilliamsQ15", ``:bool``);
(* WilliamsQ16 : Williams writes that [Q16] *)
val _ = new_constant ("WilliamsQ16", ``:bool``);

val p6_2_01 = new_axiom ("p6_2_01", ``WR ==> (!a. Member a /\ Claim a ==> Corr a)``);
val p6_2_02 = new_axiom ("p6_2_02", ``Member Ash /\ ~Corr Ash``);

Theorem p6_2_03:
  WR ==> ~Claim Ash
Proof
  metis_tac [p6_2_01, p6_2_02]
QED

val p6_2_04 = new_axiom ("p6_2_04", ``WilliamsQ15``);
val p6_2_05 = new_axiom ("p6_2_05", ``~RequiresAll``);
val p6_2_06 = new_axiom ("p6_2_06", ``WilliamsQ16``);
val p6_2_07 = new_axiom ("p6_2_07", ``SleatQ12``);
val p6_2_08 = new_axiom ("p6_2_08", ``WilliamsQ15 /\ ~RequiresAll /\ WilliamsQ16 /\ SleatQ12 ==> PointsFirst``);
val p6_2_09 = new_axiom ("p6_2_09", ``PointsFirst /\ (WR ==> ~Claim Ash) ==> SupportsBoth``);
val p6_2_10 = new_axiom ("p6_2_10", ``~WilliamsDecides``);

Theorem p6_2_11:
  (WR ==> ~Claim Ash) /\ PointsFirst /\ SupportsBoth /\ ~WilliamsDecides
Proof
  metis_tac [p6_2_01, p6_2_02, p6_2_03, p6_2_04, p6_2_05, p6_2_06, p6_2_07, p6_2_08, p6_2_09, p6_2_10]
QED


Theorem final:
  (WR ==> ~Claim Ash) /\ PointsFirst /\ SupportsBoth /\ ~WilliamsDecides
Proof
  metis_tac [p6_2_01, p6_2_02, p6_2_03, p6_2_04, p6_2_05, p6_2_06, p6_2_07, p6_2_08, p6_2_09, p6_2_10, p6_2_11]
QED

val _ = export_theory ();
