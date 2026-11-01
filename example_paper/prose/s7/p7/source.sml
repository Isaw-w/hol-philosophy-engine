open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p7";

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
(* Reason a : a has a reason of authority: a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Reason", ``:person -> bool``);
(* Corr a : a's corrected outlook gives a a reason against resisting P besides P's hold over a *)
val _ = new_constant ("Corr", ``:person -> bool``);
(* AcceptEach : the strong reading of Claim 1 holds *)
val _ = new_constant ("AcceptEach", ``:bool``);
(* EveryPathPays : every path through the tension gives up one premise of the dilemma *)
val _ = new_constant ("EveryPathPays", ``:bool``);
(* PathA : the first path, keeping the two levels apart, is taken *)
val _ = new_constant ("PathA", ``:bool``);
(* PathB : the second path, letting the group's standard govern authority over every member, is taken *)
val _ = new_constant ("PathB", ``:bool``);
(* PathC : the third path, lifting internalism to the group, is taken *)
val _ = new_constant ("PathC", ``:bool``);
(* PathD : the fourth path, lowering legitimacy to each member, is taken *)
val _ = new_constant ("PathD", ``:bool``);
(* PathE : the fifth path, cutting the link between authority and reasons, is taken *)
val _ = new_constant ("PathE", ``:bool``);
(* PathF : the sixth path, denying that the gap opens, is taken *)
val _ = new_constant ("PathF", ``:bool``);
(* CostA : on the first path a legitimate state stands to some of its members in relationships that are not political in Sleat's sense *)
val _ = new_constant ("CostA", ``:bool``);
(* Satisfaction : J can make sense to S while some member's corrected outlook gives no reason not to resist P other than P's hold *)
val _ = new_constant ("Satisfaction", ``:bool``);
(* HardMember : some member under a legitimation that makes sense is a hard case *)
val _ = new_constant ("HardMember", ``:bool``);
(* FourHold : any four of the five premises of the dilemma can hold together *)
val _ = new_constant ("FourHold", ``:bool``);
(* OnlyA : the first path alone gives up nothing Williams states *)
val _ = new_constant ("OnlyA", ``:bool``);

val p7_7_01 = new_axiom ("p7_7_01", ``AcceptEach <=> (GoesBeyond /\ MakesSense ==> !a. Member a ==> Claim a)``);

Theorem p7_7_02:
  ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\ (GoesBeyond /\ MakesSense /\ Member Ash) /\ ~Corr Ash)
Proof
  metis_tac [p7_7_01]
QED

val p7_7_03 = new_axiom ("p7_7_03", ``FourHold``);
val p7_7_04 = new_axiom ("p7_7_04", ``PathA ==> ~AcceptEach``);
val p7_7_05 = new_axiom ("p7_7_05", ``PathB ==> ~(!a. Reason a ==> Corr a)``);
val p7_7_06 = new_axiom ("p7_7_06", ``PathC ==> ~(!a. Member a /\ Claim a ==> Corr a)``);
val p7_7_07 = new_axiom ("p7_7_07", ``PathD ==> ~Satisfaction``);
val p7_7_08 = new_axiom ("p7_7_08", ``PathE ==> ~(!a. Member a /\ Claim a ==> Reason a)``);
val p7_7_09 = new_axiom ("p7_7_09", ``PathF ==> ~HardMember``);
val p7_7_10 = new_axiom ("p7_7_10", ``((PathA ==> ~AcceptEach) /\ (PathB ==> ~(!a. Reason a ==> Corr a)) /\ (PathC ==> ~(!a. Member a /\ Claim a ==> Corr a)) /\ (PathD ==> ~Satisfaction) /\ (PathE ==> ~(!a. Member a /\ Claim a ==> Reason a)) /\ (PathF ==> ~HardMember)) ==> EveryPathPays``);
val p7_7_11 = new_axiom ("p7_7_11", ``OnlyA``);
val p7_7_12 = new_axiom ("p7_7_12", ``CostA``);

Theorem p7_7_13:
  ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\ (GoesBeyond /\ MakesSense /\ Member Ash) /\ ~Corr Ash) /\ FourHold /\ ((PathA ==> ~AcceptEach) /\ (PathB ==> ~(!a. Reason a ==> Corr a)) /\ (PathC ==> ~(!a. Member a /\ Claim a ==> Corr a)) /\ (PathD ==> ~Satisfaction) /\ (PathE ==> ~(!a. Member a /\ Claim a ==> Reason a)) /\ (PathF ==> ~HardMember)) /\ EveryPathPays /\ OnlyA /\ CostA
Proof
  metis_tac [p7_7_01, p7_7_02, p7_7_03, p7_7_04, p7_7_05, p7_7_06, p7_7_07, p7_7_08, p7_7_09, p7_7_10, p7_7_11, p7_7_12]
QED


Theorem final:
  ~(AcceptEach /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\ (GoesBeyond /\ MakesSense /\ Member Ash) /\ ~Corr Ash) /\ FourHold /\ ((PathA ==> ~AcceptEach) /\ (PathB ==> ~(!a. Reason a ==> Corr a)) /\ (PathC ==> ~(!a. Member a /\ Claim a ==> Corr a)) /\ (PathD ==> ~Satisfaction) /\ (PathE ==> ~(!a. Member a /\ Claim a ==> Reason a)) /\ (PathF ==> ~HardMember)) /\ EveryPathPays /\ OnlyA /\ CostA
Proof
  metis_tac [p7_7_01, p7_7_02, p7_7_03, p7_7_04, p7_7_05, p7_7_06, p7_7_07, p7_7_08, p7_7_09, p7_7_10, p7_7_11, p7_7_12, p7_7_13]
QED

val _ = export_theory ();
