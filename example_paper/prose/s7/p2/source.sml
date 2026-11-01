open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p2";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* ExtToward a : externalism about authority holds toward a *)
val _ = new_constant ("ExtToward", ``:person -> bool``);
(* PointsFirst : Williams's treatment of dissenters, as Sleat reads it, gives his realism the strong reading *)
val _ = new_constant ("PointsFirst", ``:bool``);
(* PathB : the second path, letting the group's standard govern authority over every member, is taken *)
val _ = new_constant ("PathB", ``:bool``);
(* WilliamsCease : Williams says that those beyond blame's mechanisms are people we cease to blame (1995, 43) *)
val _ = new_constant ("WilliamsCease", ``:bool``);
(* WilliamsDoubtExt : Williams doubts that any external reason statement is true (1995, 40) *)
val _ = new_constant ("WilliamsDoubtExt", ``:bool``);
(* WilliamsNonNorm : Williams says that making sense applied to others is not normative (2005, 11) *)
val _ = new_constant ("WilliamsNonNorm", ``:bool``);
(* CostB : the second path goes against Williams's doubt about external reasons, his account of making sense applied to others, and his treatment of hard cases *)
val _ = new_constant ("CostB", ``:bool``);

val p7_2_01 = new_axiom ("p7_2_01", ``PathB ==> AcceptEach /\ (!a. Member a /\ Claim a ==> Reason a)``);
val p7_2_02 = new_axiom ("p7_2_02", ``AcceptEach ==> Claim Ash``);
val p7_2_03 = new_axiom ("p7_2_03", ``Member Ash /\ ~Corr Ash``);
val p7_2_04 = new_axiom ("p7_2_04", ``!a. ExtToward a <=> Claim a /\ ~Corr a``);

Theorem p7_2_05:
  PathB ==> ExtToward Ash /\ Reason Ash /\ ~Corr Ash
Proof
  metis_tac [p7_2_01, p7_2_02, p7_2_03, p7_2_04]
QED

val p7_2_06 = new_axiom ("p7_2_06", ``PointsFirst``);
val p7_2_07 = new_axiom ("p7_2_07", ``WilliamsDoubtExt``);
val p7_2_08 = new_axiom ("p7_2_08", ``WilliamsNonNorm``);
val p7_2_09 = new_axiom ("p7_2_09", ``WilliamsCease``);
val p7_2_10 = new_axiom ("p7_2_10", ``WilliamsDoubtExt /\ WilliamsNonNorm /\ WilliamsCease ==> CostB``);

Theorem p7_2_11:
  (PathB ==> ExtToward Ash /\ Reason Ash /\ ~Corr Ash) /\ PointsFirst /\ CostB
Proof
  metis_tac [p7_2_01, p7_2_02, p7_2_03, p7_2_04, p7_2_05, p7_2_06, p7_2_07, p7_2_08, p7_2_09, p7_2_10]
QED


Theorem final:
  (PathB ==> ExtToward Ash /\ Reason Ash /\ ~Corr Ash) /\ PointsFirst /\ CostB
Proof
  metis_tac [p7_2_01, p7_2_02, p7_2_03, p7_2_04, p7_2_05, p7_2_06, p7_2_07, p7_2_08, p7_2_09, p7_2_10, p7_2_11]
QED

val _ = export_theory ();
