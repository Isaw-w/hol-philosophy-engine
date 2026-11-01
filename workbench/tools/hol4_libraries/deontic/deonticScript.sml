(* The deontic library a formalized response may use. Carmo and Jones's dyadic deontic logic, in the shallow semantical
   embedding of Benzmueller, Farjami and Parent (2018, proved sound and complete; LogiKEy's CJ_DDL in Isabelle/HOL),
   transcribed axiom by axiom, plus knowledge (reflexive), betterness (van Benthem et al. 2009 with Halpern's lifting)
   and probability (Fagin, Halpern and Megiddo 1990), as in the checker used before. A statement has type
   world -> bool: the situations in which it holds. *)
open HolKernel Parse boolLib bossLib realTheory;

val _ = new_theory "deontic";

val _ = new_type ("world", 0);
val _ = new_constant ("cw", ``:world``);                                       (* the actual situation *)
val _ = new_constant ("av", ``:world -> world -> bool``);                      (* still possible, as things actually are *)
val _ = new_constant ("pv", ``:world -> world -> bool``);                      (* potentially possible *)
val _ = new_constant ("ob", ``:(world -> bool) -> (world -> bool) -> bool``);  (* ob X Y: in context X, Y is obligatory *)

(* Carmo and Jones's conditions, as in CJ_DDL *)
val ax_3a = new_axiom ("ax_3a", ``!w. ?x. av w x``);
val ax_4a = new_axiom ("ax_4a", ``!w x. av w x ==> pv w x``);
val ax_4b = new_axiom ("ax_4b", ``!w. pv w w``);
val ax_5a = new_axiom ("ax_5a", ``!X. ~ob X (\x. F)``);
val ax_5b = new_axiom ("ax_5b", ``!X Y Z. (!w. (Y w /\ X w) <=> (Z w /\ X w)) ==> (ob X Y <=> ob X Z)``);
val ax_5ca = new_axiom ("ax_5ca",
  ``!X (b:(world -> bool) -> bool). ((!Z. b Z ==> ob X Z) /\ (?Z. b Z)) ==>
      ((?y. (\w. !Z. b Z ==> Z w) y /\ X y) ==> ob X (\w. !Z. b Z ==> Z w))``);
val ax_5c = new_axiom ("ax_5c", ``!X Y Z. ((?w. X w /\ Y w /\ Z w) /\ ob X Y /\ ob X Z) ==> ob X (\w. Y w /\ Z w)``);
val ax_5d = new_axiom ("ax_5d",
  ``!X Y Z. ((!w. Y w ==> X w) /\ ob X Y /\ (!w. X w ==> Z w)) ==> ob Z (\w. (Z w /\ ~X w) \/ Y w)``);
val ax_5e = new_axiom ("ax_5e", ``!X Y Z. ((!w. Y w ==> X w) /\ ob X Z /\ (?w. Y w /\ Z w)) ==> ob Y Z``);

(* where a statement holds *)
val Now_def = Define `Now (A:world -> bool) = A cw`;                             (* in the actual situation *)
val Valid_def = Define `Valid (A:world -> bool) = !w. A w`;                      (* in every situation *)

(* obligation, possibility *)
val Ought_def = Define `Ought (B:world -> bool) (A:world -> bool) (w:world) = ob A B`;            (* B ought to be, given A *)
val OughtNow_def = Define `OughtNow (A:world -> bool) (w:world) = (ob (av w) A /\ ?x. av w x /\ ~A x)`;  (* A ought to be now *)
val Can_def = Define `Can (A:world -> bool) (w:world) = ?x. av w x /\ A x`;     (* A can still come about *)
val Settled_def = Define `Settled (A:world -> bool) (w:world) = !x. av w x ==> A x`;   (* A holds however things go now *)

(* knowledge: the assistant knows A *)
val _ = new_constant ("epi", ``:world -> world -> bool``);
val epi_refl = new_axiom ("epi_refl", ``!w. epi w w``);
val Knows_def = Define `Knows (A:world -> bool) (w:world) = !v. epi w v ==> A v`;

(* betterness: BR v w = w is at least as good as v *)
val _ = new_constant ("BR", ``:world -> world -> bool``);
val br_refl = new_axiom ("br_refl", ``!x. BR x x``);
val br_trans = new_axiom ("br_trans", ``!x y z. BR x y /\ BR y z ==> BR x z``);
val br_limit = new_axiom ("br_limit",
  ``!A:world -> bool. (?w. A w) ==> ?w. A w /\ !v. A v ==> ~(BR w v /\ ~BR v w)``);
val Better_def = Define `Better (A:world -> bool) (B:world -> bool) (w:world) =
  !s. B s ==> ?t. A t /\ BR s t /\ ~BR t s`;                                      (* A is better than B *)

(* probability on statements *)
val _ = new_constant ("Pr", ``:(world -> bool) -> real``);
val pr_top = new_axiom ("pr_top", ``Pr (\w. T) = 1``);
val pr_nonneg = new_axiom ("pr_nonneg", ``!A. 0 <= Pr A``);
val pr_add = new_axiom ("pr_add", ``!A B. (!w. ~(A w /\ B w)) ==> Pr (\w. A w \/ B w) = Pr A + Pr B``);
val PrIf_def = Define `PrIf (A:world -> bool) (B:world -> bool) = Pr (\w. A w /\ B w) / Pr B`;   (* probability of A given B *)

(* derived rules, proved here so a response can cite them *)
Theorem detach:
  !A B w. Valid (Ought A B) /\ Settled B w /\ Can A w /\ Can (\x. ~A x) w ==> OughtNow A w
Proof
  rw[Valid_def, Ought_def, Settled_def, Can_def, OughtNow_def] >>
  irule (ax_5e |> SPEC_ALL |> UNDISCH_ALL |> DISCH_ALL |> GEN_ALL) >> metis_tac[]
QED

Theorem settled_not_ought:
  !A w. Settled A w ==> ~OughtNow A w
Proof
  rw[Settled_def, OughtNow_def] >> metis_tac[]
QED

val _ = export_theory ();
