open HolKernel Parse boolLib bossLib;
val _ = new_theory "dsp2_s2p3";

(* GroupInternal : making sense is internal to S: Claim 3 judges J by S's outlook in C(S), and nothing in it is a standard independent of S's outlook that justifies P *)
val _ = new_constant ("GroupInternal", ``:bool``);
(* KeepOurs : being S, in the condition that J would make sense to us if we were S, leaves us with our own beliefs *)
val _ = new_constant ("KeepOurs", ``:bool``);
(* SomeFalseMS : something that does not make sense to us because we take it to be false made sense to an earlier society *)
val _ = new_constant ("SomeFalseMS", ``:bool``);
(* CondANotJust : condition (a) says not much more than that coercion requires legitimation and that the will of the stronger is not itself one, and does not settle what justifies P *)
val _ = new_constant ("CondANotJust", ``:bool``);
(* DefLevels : a standard is internal to a person or a group when their outlook settles whether it is met, and external to them, or independent of their outlook, when it does not *)
val _ = new_constant ("DefLevels", ``:bool``);
(* WilliamsFalse11 : Williams allows that some of what made sense to earlier societies does not make sense to us because we take it to be false (2005, 11) *)
val _ = new_constant ("WilliamsFalse11", ``:bool``);
(* WilliamsAxiom : Williams says that might does not imply right (2005, 5-6), and that the universal paradigm of injustice, simply in this form, is indeterminate about what it requires and says not much more than that coercion requires legitimation and that the will of the stronger is not itself a legitimation (2005, 23) *)
val _ = new_constant ("WilliamsAxiom", ``:bool``);
(* WilliamsOurCase : Williams says that what makes most sense to us is a structure of authority that we think we should accept (2005, 11) *)
val _ = new_constant ("WilliamsOurCase", ``:bool``);
(* WilliamsQ2 : Williams writes that [Q2] *)
val _ = new_constant ("WilliamsQ2", ``:bool``);

val p2_3_01 = new_axiom ("p2_3_01", ``DefLevels``);
val p2_3_02 = new_axiom ("p2_3_02", ``WilliamsQ2``);
val p2_3_03 = new_axiom ("p2_3_03", ``WilliamsQ2 ==> (KeepOurs ==> ~SomeFalseMS)``);
val p2_3_04 = new_axiom ("p2_3_04", ``WilliamsFalse11``);
val p2_3_05 = new_axiom ("p2_3_05", ``WilliamsFalse11 ==> SomeFalseMS``);

Theorem p2_3_06:
  ~KeepOurs
Proof
  metis_tac [p2_3_01, p2_3_02, p2_3_03, p2_3_04, p2_3_05]
QED

val p2_3_07 = new_axiom ("p2_3_07", ``WilliamsAxiom``);
val p2_3_08 = new_axiom ("p2_3_08", ``WilliamsAxiom ==> CondANotJust``);
val p2_3_09 = new_axiom ("p2_3_09", ``DefLevels /\ ~KeepOurs /\ CondANotJust ==> GroupInternal``);
val p2_3_10 = new_axiom ("p2_3_10", ``WilliamsOurCase``);

Theorem p2_3_11:
  GroupInternal /\ WilliamsOurCase
Proof
  metis_tac [p2_3_01, p2_3_02, p2_3_03, p2_3_04, p2_3_05, p2_3_06, p2_3_07, p2_3_08, p2_3_09, p2_3_10]
QED


Theorem final:
  GroupInternal /\ WilliamsOurCase
Proof
  metis_tac [p2_3_01, p2_3_02, p2_3_03, p2_3_04, p2_3_05, p2_3_06, p2_3_07, p2_3_08, p2_3_09, p2_3_10, p2_3_11]
QED

val _ = export_theory ();
