open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s8p1";

val _ = new_type ("person", 0);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* Claim a : P's claim of authority over a is true *)
val _ = new_constant ("Claim", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
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
(* Owes : realism in Williams's form owes an account of whose outlook a claim of authority answers to *)
val _ = new_constant ("Owes", ``:bool``);
(* FourHold : any four of the five premises of the dilemma can hold together *)
val _ = new_constant ("FourHold", ``:bool``);

val p8_1_01 = new_axiom ("p8_1_01", ``GroupInternal``);
val p8_1_02 = new_axiom ("p8_1_02", ``WR ==> (!a. Member a /\ Claim a ==> Corr a)``);
val p8_1_03 = new_axiom ("p8_1_03", ``!a. Member a ==> ExtToMember a``);
val p8_1_04 = new_axiom ("p8_1_04", ``~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a))``);
val p8_1_05 = new_axiom ("p8_1_05", ``SupportsBoth``);
val p8_1_06 = new_axiom ("p8_1_06", ``~WilliamsDecides``);
val p8_1_07 = new_axiom ("p8_1_07", ``FourHold``);
val p8_1_08 = new_axiom ("p8_1_08", ``EveryPathPays``);
val p8_1_09 = new_axiom ("p8_1_09", ``~WilliamsDecides /\ EveryPathPays ==> Owes``);

Theorem p8_1_10:
  Owes
Proof
  metis_tac [p8_1_01, p8_1_02, p8_1_03, p8_1_04, p8_1_05, p8_1_06, p8_1_07, p8_1_08, p8_1_09]
QED


Theorem p8_1_11:
  GroupInternal /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ (!a. Member a ==> ExtToMember a) /\ ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a)) /\ SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays /\ Owes
Proof
  metis_tac [p8_1_01, p8_1_02, p8_1_03, p8_1_04, p8_1_05, p8_1_06, p8_1_07, p8_1_08, p8_1_09, p8_1_10]
QED


Theorem final:
  GroupInternal /\ (WR ==> (!a. Member a /\ Claim a ==> Corr a)) /\ (!a. Member a ==> ExtToMember a) /\ ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Corr a)) /\ SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays /\ Owes
Proof
  metis_tac [p8_1_01, p8_1_02, p8_1_03, p8_1_04, p8_1_05, p8_1_06, p8_1_07, p8_1_08, p8_1_09, p8_1_10, p8_1_11]
QED

val _ = export_theory ();
