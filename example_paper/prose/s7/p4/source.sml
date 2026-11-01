open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p4";

(* PathD : the fourth path, lowering legitimacy to each member, is taken *)
val _ = new_constant ("PathD", ``:bool``);
(* IndivLegit : for legitimacy, J must make sense to each member's corrected outlook, and P is legitimate to the degree that it does *)
val _ = new_constant ("IndivLegit", ``:bool``);
(* Satisfaction : J can make sense to S while some member's corrected outlook gives no reason not to resist P other than P's hold *)
val _ = new_constant ("Satisfaction", ``:bool``);
(* WilliamsEach : Williams says there is a sense in which the demand requires a legitimation to be given to every subject (2005, 6), speaks of acceptability to each subject (2005, 7) and treats the considerations that support legitimacy as scalar (2005, 10) *)
val _ = new_constant ("WilliamsEach", ``:bool``);
(* CostD : the fourth path goes against Williams's denial that meeting the demand requires everyone's acceptance *)
val _ = new_constant ("CostD", ``:bool``);
(* DTogether : on the fourth path internalism about authority and the strong reading can hold together *)
val _ = new_constant ("DTogether", ``:bool``);
(* WilliamsQ3 : Williams writes that [Q3] *)
val _ = new_constant ("WilliamsQ3", ``:bool``);

val p7_4_01 = new_axiom ("p7_4_01", ``PathD ==> IndivLegit /\ ~Satisfaction``);
val p7_4_02 = new_axiom ("p7_4_02", ``DTogether``);
val p7_4_03 = new_axiom ("p7_4_03", ``WilliamsEach``);
val p7_4_04 = new_axiom ("p7_4_04", ``WilliamsQ3``);
val p7_4_05 = new_axiom ("p7_4_05", ``WilliamsQ3 ==> CostD``);

Theorem p7_4_06:
  (PathD ==> IndivLegit /\ ~Satisfaction) /\ DTogether /\ WilliamsEach /\ CostD
Proof
  metis_tac [p7_4_01, p7_4_02, p7_4_03, p7_4_04, p7_4_05]
QED


Theorem final:
  (PathD ==> IndivLegit /\ ~Satisfaction) /\ DTogether /\ WilliamsEach /\ CostD
Proof
  metis_tac [p7_4_01, p7_4_02, p7_4_03, p7_4_04, p7_4_05, p7_4_06]
QED

val _ = export_theory ();
