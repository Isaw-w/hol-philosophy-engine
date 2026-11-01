open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s6p1";

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
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* GroupInternal : making sense is internal to S: Claim 3 judges J by S's outlook in C(S), and nothing in it is a standard independent of S's outlook that justifies P *)
val _ = new_constant ("GroupInternal", ``:bool``);
(* ExtToMember a : J's making sense to S is a standard independent of a's outlook *)
val _ = new_constant ("ExtToMember", ``:person -> bool``);

val p6_1_01 = new_axiom ("p6_1_01", ``GroupInternal /\ ExtToMember Ash``);
val p6_1_02 = new_axiom ("p6_1_02", ``AcceptEach <=> (GoesBeyond /\ MakesSense ==> !a. Member a ==> Claim a)``);

Theorem p6_1_03:
  (AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a)) ==> (GoesBeyond /\ MakesSense ==> !a. Member a ==> Corr a)
Proof
  metis_tac [p6_1_01, p6_1_02]
QED

val p6_1_04 = new_axiom ("p6_1_04", ``GoesBeyond /\ MakesSense /\ Member Ash /\ ~Corr Ash``);

Theorem p6_1_05:
  ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a))
Proof
  metis_tac [p6_1_01, p6_1_02, p6_1_03, p6_1_04]
QED


Theorem p6_1_06:
  (GroupInternal /\ ExtToMember Ash) /\ ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a))
Proof
  metis_tac [p6_1_01, p6_1_02, p6_1_03, p6_1_04, p6_1_05]
QED


Theorem final:
  (GroupInternal /\ ExtToMember Ash) /\ ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a))
Proof
  metis_tac [p6_1_01, p6_1_02, p6_1_03, p6_1_04, p6_1_05, p6_1_06]
QED

val _ = export_theory ();
