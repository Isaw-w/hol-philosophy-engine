open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s2p4";

val _ = new_type ("person", 0);
(* Member a : a lives under P *)
val _ = new_constant ("Member", ``:person -> bool``);
(* RequiresAll : universal acceptance is required for meeting the demand *)
val _ = new_constant ("RequiresAll", ``:bool``);
(* ExtToMember a : J's making sense to S is a standard independent of a's outlook *)
val _ = new_constant ("ExtToMember", ``:person -> bool``);
(* DefLevels : a standard is internal to a person or a group when their outlook settles whether it is met, and external to them, or independent of their outlook, when it does not *)
val _ = new_constant ("DefLevels", ``:bool``);
(* ReadsS : Claim 3 reads the outlook of S, not that of any one member *)
val _ = new_constant ("ReadsS", ``:bool``);
(* WilliamsFanatics : Williams says that a legitimation can stop making sense while the truly fanatical can still bring themselves to believe it (2005, 71) *)
val _ = new_constant ("WilliamsFanatics", ``:bool``);
(* WilliamsQ4 : Williams writes that [Q4] *)
val _ = new_constant ("WilliamsQ4", ``:bool``);

val p2_4_01 = new_axiom ("p2_4_01", ``WilliamsFanatics``);
val p2_4_02 = new_axiom ("p2_4_02", ``WilliamsQ4``);
val p2_4_03 = new_axiom ("p2_4_03", ``~RequiresAll``);
val p2_4_04 = new_axiom ("p2_4_04", ``ReadsS``);
val p2_4_05 = new_axiom ("p2_4_05", ``DefLevels``);
val p2_4_06 = new_axiom ("p2_4_06", ``WilliamsFanatics /\ WilliamsQ4 /\ ~RequiresAll /\ ReadsS /\ DefLevels ==> (!a. Member a ==> ExtToMember a)``);

Theorem p2_4_07:
  !a. Member a ==> ExtToMember a
Proof
  metis_tac [p2_4_01, p2_4_02, p2_4_03, p2_4_04, p2_4_05, p2_4_06]
QED


Theorem final:
  !a. Member a ==> ExtToMember a
Proof
  metis_tac [p2_4_01, p2_4_02, p2_4_03, p2_4_04, p2_4_05, p2_4_06, p2_4_07]
QED

val _ = export_theory ();
