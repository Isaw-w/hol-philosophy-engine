open HolKernel Parse boolLib bossLib;
val _ = new_theory "dissenter_core";

(* Core argument of "Does Making Sense Bind the Dissenter?", in the shared language.
   Everything is quantified over the persons and predicates, so no premise is asserted.
     Member a : a lives under P
     Claim a  : P's claim of authority over a is true
     Reason a : a has a reason not to resist P other than P's hold over a (a reason of authority)
     Corr a   : a's corrected outlook gives a such a reason
     GB       : J goes beyond the assertion of P
     MS       : J makes sense to S
     d        : the dissenter (Ash)
   The five premises of the dilemma, in Ash's case.
     Strong reading (Claim 1 over every member):  GB /\ MS ==> !a. Member a ==> Claim a
     Reasons of authority (Williams 2005: 6):      !a. Member a /\ Claim a ==> Reason a
     Internalism (Williams 1995: 35):              !a. Reason a ==> Corr a
     Satisfaction (Williams 2005: 135-136):        GB /\ MS /\ Member d
     Hard case (Williams 1995: 43):                ~Corr d *)

(* The five premises cannot all hold. *)
Theorem dilemma_premises_inconsistent:
  !(Member:'a -> bool) Claim Reason Corr GB MS d.
    ~((GB /\ MS ==> !a. Member a ==> Claim a) /\
      (!a. Member a /\ Claim a ==> Reason a) /\
      (!a. Reason a ==> Corr a) /\
      (GB /\ MS /\ Member d) /\
      ~Corr d)
Proof
  metis_tac []
QED

(* The dilemma without internalism: either some reason of authority is external, or the strong reading fails. *)
Theorem dilemma_without_internalism:
  !(Member:'a -> bool) Claim Reason Corr GB MS d.
    (!a. Member a /\ Claim a ==> Reason a) /\ (GB /\ MS /\ Member d) /\ ~Corr d ==>
    (?a. Reason a /\ ~Corr a) \/ ~(GB /\ MS ==> !a. Member a ==> Claim a)
Proof
  metis_tac []
QED

(* The strong reading joined to internalism about authority makes the group's standard fix every member's
   corrected outlook: if J makes sense to S, every member's corrected outlook gives a reason of authority. *)
Theorem strong_reading_fixes_every_outlook:
  !(Member:'a -> bool) Claim Reason Corr GB MS.
    (GB /\ MS ==> !a. Member a ==> Claim a) /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) ==>
    (GB /\ MS ==> !a. Member a ==> Corr a)
Proof
  metis_tac []
QED

(* Any four of the five premises can hold together. *)

(* Without the strong reading (first path); P's claim of authority is still true over another member. *)
Theorem four_without_strong_reading:
  ?(Member:num -> bool) Claim Reason Corr GB MS d.
    (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\ (GB /\ MS /\ Member d) /\ ~Corr d /\
    (?a. Member a /\ Claim a)
Proof
  qexistsl_tac [`\a. T`, `\a. a = 1`, `\a. a = 1`, `\a. a = 1`, `T`, `T`, `0`] >> rw []
QED

(* Without internalism (second and third paths). *)
Theorem four_without_internalism:
  ?(Member:num -> bool) Claim Reason Corr GB MS d.
    (GB /\ MS ==> !a. Member a ==> Claim a) /\ (!a. Member a /\ Claim a ==> Reason a) /\ (GB /\ MS /\ Member d) /\ ~Corr d
Proof
  qexistsl_tac [`\a. T`, `\a. T`, `\a. T`, `\a. F`, `T`, `T`, `0`] >> rw []
QED

(* Without satisfaction (fourth path): J fails to make sense to S, for legitimacy, while a member lacks the reason. *)
Theorem four_without_satisfaction:
  ?(Member:num -> bool) Claim Reason Corr GB MS d.
    (GB /\ MS ==> !a. Member a ==> Claim a) /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\
    Member d /\ ~Corr d
Proof
  qexistsl_tac [`\a. T`, `\a. F`, `\a. F`, `\a. F`, `T`, `F`, `0`] >> rw []
QED

(* Without reasons of authority (fifth path): the claim over the dissenter is true and gives no reason. *)
Theorem four_without_reasons_of_authority:
  ?(Member:num -> bool) Claim Reason Corr GB MS d.
    (GB /\ MS ==> !a. Member a ==> Claim a) /\ (!a. Reason a ==> Corr a) /\ (GB /\ MS /\ Member d) /\ ~Corr d /\
    Claim d /\ ~Reason d
Proof
  qexistsl_tac [`\a. T`, `\a. T`, `\a. F`, `\a. F`, `T`, `T`, `0`] >> rw []
QED

(* Without the hard case (sixth path). *)
Theorem four_without_hard_case:
  ?(Member:num -> bool) Claim Reason Corr GB MS d.
    (GB /\ MS ==> !a. Member a ==> Claim a) /\ (!a. Member a /\ Claim a ==> Reason a) /\ (!a. Reason a ==> Corr a) /\
    (GB /\ MS /\ Member d)
Proof
  qexistsl_tac [`\a. T`, `\a. T`, `\a. T`, `\a. T`, `T`, `T`, `0`] >> rw []
QED

val _ = export_theory ();
