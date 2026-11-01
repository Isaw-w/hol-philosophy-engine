open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p3";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* ExtToward a : externalism about authority holds toward a *)
val _ = new_constant ("ExtToward", ``:person -> bool``);
(* WilliamsOurCase : Williams says that what makes most sense to us is a structure of authority that we think we should accept (2005, 11) *)
val _ = new_constant ("WilliamsOurCase", ``:bool``);
(* PathC : the third path, lifting internalism to the group, is taken *)
val _ = new_constant ("PathC", ``:bool``);
(* GroupReason : reasons of authority belong to S, and a member has them as one of S *)
val _ = new_constant ("GroupReason", ``:bool``);
(* WilliamsAudience : Williams says that the theorist speaks to an audience who share these conceptions of reasonableness or whom the theorist hopes to persuade (2005, 136) *)
val _ = new_constant ("WilliamsAudience", ``:bool``);
(* CostC : the third path goes against Williams's internalism about each person and leaves Ash outside the audience *)
val _ = new_constant ("CostC", ``:bool``);
(* WilliamsQ9 : Williams writes that [Q9] *)
val _ = new_constant ("WilliamsQ9", ``:bool``);

val p7_3_01 = new_axiom ("p7_3_01", ``PathC ==> GroupReason /\ AcceptEach``);
val p7_3_02 = new_axiom ("p7_3_02", ``AcceptEach ==> Claim Ash``);
val p7_3_03 = new_axiom ("p7_3_03", ``~Corr Ash``);
val p7_3_04 = new_axiom ("p7_3_04", ``!a. ExtToward a <=> Claim a /\ ~Corr a``);

Theorem p7_3_05:
  PathC ==> GroupReason /\ ExtToward Ash
Proof
  metis_tac [p7_3_01, p7_3_02, p7_3_03, p7_3_04]
QED

val p7_3_06 = new_axiom ("p7_3_06", ``WilliamsOurCase``);
val p7_3_07 = new_axiom ("p7_3_07", ``WilliamsQ9``);
val p7_3_08 = new_axiom ("p7_3_08", ``WilliamsAudience``);
val p7_3_09 = new_axiom ("p7_3_09", ``WilliamsQ9 /\ WilliamsAudience ==> CostC``);

Theorem p7_3_10:
  (PathC ==> GroupReason /\ ExtToward Ash) /\ WilliamsOurCase /\ CostC
Proof
  metis_tac [p7_3_01, p7_3_02, p7_3_03, p7_3_04, p7_3_05, p7_3_06, p7_3_07, p7_3_08, p7_3_09]
QED


Theorem final:
  (PathC ==> GroupReason /\ ExtToward Ash) /\ WilliamsOurCase /\ CostC
Proof
  metis_tac [p7_3_01, p7_3_02, p7_3_03, p7_3_04, p7_3_05, p7_3_06, p7_3_07, p7_3_08, p7_3_09, p7_3_10]
QED

val _ = export_theory ();
