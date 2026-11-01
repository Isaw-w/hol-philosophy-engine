open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s7p6";

(* PathF : the sixth path, denying that the gap opens, is taken *)
val _ = new_constant ("PathF", ``:bool``);
(* HardMember : some member under a legitimation that makes sense is a hard case *)
val _ = new_constant ("HardMember", ``:bool``);
(* WilliamsProlepsis : Williams says that very powerful political discourse can be proleptic (2005, 26) and that blame works proleptically through a disposition to have the respect of others (1995, 41-42) *)
val _ = new_constant ("WilliamsProlepsis", ``:bool``);
(* CostF : the sixth path goes against Williams's hard cases and his anarchists and utterly unreasonable *)
val _ = new_constant ("CostF", ``:bool``);
(* WilliamsQ3 : Williams writes that [Q3] *)
val _ = new_constant ("WilliamsQ3", ``:bool``);
(* WilliamsQ11 : Williams writes that [Q11] *)
val _ = new_constant ("WilliamsQ11", ``:bool``);

val p7_6_01 = new_axiom ("p7_6_01", ``PathF ==> ~HardMember``);
val p7_6_02 = new_axiom ("p7_6_02", ``WilliamsProlepsis``);
val p7_6_03 = new_axiom ("p7_6_03", ``WilliamsQ11``);
val p7_6_04 = new_axiom ("p7_6_04", ``WilliamsQ3``);
val p7_6_05 = new_axiom ("p7_6_05", ``WilliamsQ11 /\ WilliamsQ3 ==> CostF``);

Theorem p7_6_06:
  (PathF ==> ~HardMember) /\ WilliamsProlepsis /\ CostF
Proof
  metis_tac [p7_6_01, p7_6_02, p7_6_03, p7_6_04, p7_6_05]
QED


Theorem final:
  (PathF ==> ~HardMember) /\ WilliamsProlepsis /\ CostF
Proof
  metis_tac [p7_6_01, p7_6_02, p7_6_03, p7_6_04, p7_6_05, p7_6_06]
QED

val _ = export_theory ();
