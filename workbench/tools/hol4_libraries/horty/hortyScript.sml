(* Reasons as defaults: Horty's fixed-priority default theories (Reasons as Defaults, OUP 2012; ILLC slides 2011),
   for formalized responses. Formulas are data (atoms named by strings), so that both "follows" and "does not follow"
   are decided by HOL4's own evaluation, and every verdict is a kernel theorem.

   A default theory: facts W (formulas), defaults D (name, premise, conclusion), a priority P (weaker, stronger).
   For a scenario S (the names of some defaults, in D's order):
     Triggered  : W plus the conclusions of S entail the premise
     Conflicted : W plus the conclusions of S entail the negation of the conclusion
     Defeated   : some triggered default that is stronger has a conclusion that, with W, entails the negation of this one
     Binding    : triggered, not conflicted, not defeated
     Proper     : S is exactly the binding defaults (stable), and every default in S is reached step by step from W
                  (grounded; Horty's fix for self-supporting defaults)
   OughtH A    : A follows from W and the conclusions of some proper scenario (Horty's conflict account)
   RequiredH A : there is a proper scenario, and A follows in every one (the disjunctive/skeptical account)        *)
open HolKernel Parse boolLib bossLib listTheory combinTheory stringTheory;

val _ = new_theory "horty";

Datatype:
  form = Atom string | Neg form | Conj form form | Disj form form | Impl form form | Tru
End

Definition evalf_def:
  (evalf v (Atom s) = v s) /\ (evalf v (Neg f) = ~evalf v f) /\
  (evalf v (Conj f g) = (evalf v f /\ evalf v g)) /\ (evalf v (Disj f g) = (evalf v f \/ evalf v g)) /\
  (evalf v (Impl f g) = (evalf v f ==> evalf v g)) /\ (evalf v Tru = T)
End

Definition atoms_def:
  (atoms (Atom s) = [s]) /\ (atoms (Neg f) = atoms f) /\ (atoms (Conj f g) = atoms f ++ atoms g) /\
  (atoms (Disj f g) = atoms f ++ atoms g) /\ (atoms (Impl f g) = atoms f ++ atoms g) /\ (atoms Tru = [])
End

(* every assignment to the listed atoms (all other atoms false) *)
Definition vals_def:
  (vals [] = [(\s:string. F)]) /\
  (vals (a::as) = FLAT (MAP (\v. [v; (a =+ T) v]) (vals as)))
End

(* G entails f: f is true under every assignment to the atoms that makes all of G true *)
Definition entails_def:
  entails G f = EVERY (\v. EVERY (evalf v) G ==> evalf v f) (vals (nub (FLAT (MAP atoms (f::G)))))
End

Definition dname_def: dname (n:string, p:form, c:form) = n
End
Definition dprem_def: dprem (n:string, p:form, c:form) = p
End
Definition dconc_def: dconc (n:string, p:form, c:form) = c
End

(* the conclusions of the defaults named in S *)
Definition concs_def:
  concs D S = MAP dconc (FILTER (\d. MEM (dname d) S) D)
End

Definition triggered_def:
  triggered W D S d = entails (W ++ concs D S) (dprem d)
End
Definition conflicted_def:
  conflicted W D S d = entails (W ++ concs D S) (Neg (dconc d))
End
Definition defeated_def:
  defeated W D P S d =
    EXISTS (\e. MEM (dname d, dname e) P /\ triggered W D S e /\ entails (W ++ [dconc e]) (Neg (dconc d))) D
End
Definition binding_def:
  binding W D P S d = (triggered W D S d /\ ~conflicted W D S d /\ ~defeated W D P S d)
End

(* grounded: starting from nothing, repeatedly add the defaults of S whose premises follow; all of S is reached *)
Definition reach_def:
  (reach W D S R 0 = R) /\
  (reach W D S R (SUC k) =
     reach W D S (MAP dname (FILTER (\d. MEM (dname d) S /\ (MEM (dname d) R \/ entails (W ++ concs D R) (dprem d))) D)) k)
End
Definition proper_def:
  proper W D P S =
    (S = MAP dname (FILTER (binding W D P S) D) /\ EVERY (\n. MEM n (reach W D S [] (LENGTH D))) S)
End

(* every scenario: each sublist of D's names, in D's order *)
Definition sublists_def:
  (sublists [] = [[]]) /\ (sublists (x::xs) = FLAT (MAP (\s. [s; x::s]) (sublists xs)))
End

Definition OughtH_def:
  OughtH W D P f = EXISTS (\S. proper W D P S /\ entails (W ++ concs D S) f) (sublists (MAP dname D))
End
Definition RequiredH_def:
  RequiredH W D P f =
    (EXISTS (proper W D P) (sublists (MAP dname D)) /\
     EVERY (\S. proper W D P S ==> entails (W ++ concs D S) f) (sublists (MAP dname D)))
End
Definition ProperScenarios_def:
  ProperScenarios W D P = FILTER (proper W D P) (sublists (MAP dname D))
End

val _ = export_theory ();
