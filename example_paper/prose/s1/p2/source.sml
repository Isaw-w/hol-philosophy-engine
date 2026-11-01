open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s1p2";

val _ = new_type ("person", 0);
(* Ash : Ash *)
val _ = new_constant ("Ash", ``:person``);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* GoesBeyond : J goes beyond the assertion of P *)
val _ = new_constant ("GoesBeyond", ``:bool``);
(* MakesSense : J makes sense to S as a legitimation *)
val _ = new_constant ("MakesSense", ``:bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* Rejects a : a rejects J *)
val _ = new_constant ("Rejects", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* ExtToward a : externalism about authority holds toward a *)
val _ = new_constant ("ExtToward", ``:person -> bool``);
(* WR : Williams's realism holds *)
val _ = new_constant ("WR", ``:bool``);
(* GroupInternal : making sense is internal to S: Claim 3 judges J by S's outlook in C(S), and nothing in it is a standard independent of S's outlook that justifies P *)
val _ = new_constant ("GroupInternal", ``:bool``);
(* ExtToMember a : J's making sense to S is a standard independent of a's outlook *)
val _ = new_constant ("ExtToMember", ``:person -> bool``);

val p1_2_01 = new_axiom ("p1_2_01", ``GroupInternal``);
val p1_2_02 = new_axiom ("p1_2_02", ``!a. Member a ==> ExtToMember a``);
val p1_2_03 = new_axiom ("p1_2_03", ``WR ==> (!a. Member a /\ Claim a ==> Corr a)``);
val p1_2_04 = new_axiom ("p1_2_04", ``(Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach``);

Theorem p1_2_05:
  GroupInternal /\ (!a. Member a ==> ExtToMember a) /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ ((Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach)
Proof
  metis_tac [p1_2_01, p1_2_02, p1_2_03, p1_2_04]
QED


Theorem final:
  GroupInternal /\ (!a. Member a ==> ExtToMember a) /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ ((Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach)
Proof
  metis_tac [p1_2_01, p1_2_02, p1_2_03, p1_2_04, p1_2_05]
QED

val _ = export_theory ();
