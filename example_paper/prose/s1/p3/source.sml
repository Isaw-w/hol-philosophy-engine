open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s1p3";

(* SupportsBoth : Williams's texts support both horns of the dilemma *)
val _ = new_constant ("SupportsBoth", ``:bool``);
(* WilliamsDecides : in the 1995 essay or the 2005 book, Williams says whether a legitimate state has authority over a member whose own outlook gives no reason of authority *)
val _ = new_constant ("WilliamsDecides", ``:bool``);
(* EveryPathPays : every path through the tension gives up one premise of the dilemma *)
val _ = new_constant ("EveryPathPays", ``:bool``);
(* Plan : the paper proceeds as its opening sets out *)
val _ = new_constant ("Plan", ``:bool``);
(* FourHold : any four of the five premises of the dilemma can hold together *)
val _ = new_constant ("FourHold", ``:bool``);

val p1_3_01 = new_axiom ("p1_3_01", ``SupportsBoth``);
val p1_3_02 = new_axiom ("p1_3_02", ``~WilliamsDecides``);
val p1_3_03 = new_axiom ("p1_3_03", ``FourHold``);
val p1_3_04 = new_axiom ("p1_3_04", ``EveryPathPays``);
val p1_3_05 = new_axiom ("p1_3_05", ``Plan``);

Theorem p1_3_06:
  SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays /\ Plan
Proof
  metis_tac [p1_3_01, p1_3_02, p1_3_03, p1_3_04, p1_3_05]
QED


Theorem final:
  SupportsBoth /\ ~WilliamsDecides /\ FourHold /\ EveryPathPays /\ Plan
Proof
  metis_tac [p1_3_01, p1_3_02, p1_3_03, p1_3_04, p1_3_05, p1_3_06]
QED

val _ = export_theory ();
