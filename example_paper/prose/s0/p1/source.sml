open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s0p1";

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
(* SupportsBoth : Williams's texts support both horns of the dilemma *)
val _ = new_constant ("SupportsBoth", ``:bool``);
(* WilliamsDecides : in the 1995 essay or the 2005 book, Williams says whether a legitimate state has authority over a member whose own outlook gives no reason of authority *)
val _ = new_constant ("WilliamsDecides", ``:bool``);
(* EveryPathPays : every path through the tension gives up one premise of the dilemma *)
val _ = new_constant ("EveryPathPays", ``:bool``);
(* FourHold : any four of the five premises of the dilemma can hold together *)
val _ = new_constant ("FourHold", ``:bool``);

val p0_1_01 = new_axiom ("p0_1_01", ``GoesBeyond /\ MakesSense ==> Legit``);
val p0_1_02 = new_axiom ("p0_1_02", ``GroupInternal``);
val p0_1_03 = new_axiom ("p0_1_03", ``!a. Member a ==> ExtToMember a``);
val p0_1_04 = new_axiom ("p0_1_04", ``WR ==> (!a. Member a /\ Claim a ==> Corr a)``);
val p0_1_05 = new_axiom ("p0_1_05", ``(Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach``);
val p0_1_06 = new_axiom ("p0_1_06", ``SupportsBoth``);
val p0_1_07 = new_axiom ("p0_1_07", ``~WilliamsDecides``);
val p0_1_08 = new_axiom ("p0_1_08", ``FourHold``);
val p0_1_09 = new_axiom ("p0_1_09", ``EveryPathPays``);

Theorem p0_1_10:
  (GoesBeyond /\ MakesSense ==> Legit) /\ GroupInternal /\ (!a. Member a ==> ExtToMember a) /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ ((Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach) /\ SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays
Proof
  metis_tac [p0_1_01, p0_1_02, p0_1_03, p0_1_04, p0_1_05, p0_1_06, p0_1_07, p0_1_08, p0_1_09]
QED


Theorem final:
  (GoesBeyond /\ MakesSense ==> Legit) /\ GroupInternal /\ (!a. Member a ==> ExtToMember a) /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ ((Member Ash /\ Rejects Ash /\ GoesBeyond /\ MakesSense /\ ~Corr Ash) ==> ExtToward Ash \/ ~AcceptEach) /\ SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays
Proof
  metis_tac [p0_1_01, p0_1_02, p0_1_03, p0_1_04, p0_1_05, p0_1_06, p0_1_07, p0_1_08, p0_1_09, p0_1_10]
QED

val _ = export_theory ();
