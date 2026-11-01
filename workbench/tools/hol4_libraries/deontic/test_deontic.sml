(* Tests of the deontic library, used as a response would use it. Run in a HOL4 session with the library on loadPath. *)
load "deonticTheory"; open deonticTheory;

(* T2: a general principle "for every x, R x ought to be, given S x" detaches for a settled case *)
val T2 = prove(
  ``!(R:'a -> world -> bool) S u w. Valid (\v. !x. Ought (R x) (S x) v) /\ Settled (S u) w /\ Can (R u) w /\ Can (\v. ~R u v) w
       ==> OughtNow (R u) w``,
  rw[Valid_def] >> irule detach >> fs[Ought_def, Valid_def] >> metis_tac[]);

(* T4: a general and a more specific conditional obligation that conflict: both detach, a dilemma *)
val T4 = prove(
  ``!A B C w. Valid (Ought A B) /\ Valid (Ought (\v. ~A v) (\v. B v /\ C v)) /\ Settled (\v. B v /\ C v) w
       /\ Can A w /\ Can (\v. ~A v) w ==> OughtNow A w /\ OughtNow (\v. ~A v) w``,
  rpt strip_tac
  >- (match_mp_tac detach >> qexists_tac `B` >> fs[Settled_def])
  >- (match_mp_tac detach >> qexists_tac `\v. B v /\ C v` >> fs[Can_def] >> metis_tac[]));

(* T6: a settled fact is not an obligation now *)
val T6 = prove(``!A. Settled A cw ==> ~OughtNow A cw``, metis_tac[settled_not_ought]);

(* P6: the "obligations split" law, if added, makes every actual obligation false *)
val P6 = prove(
  ``(!w A B. OughtNow (\v. A v /\ B v) w ==> OughtNow A w) ==> !X. ~OughtNow X cw``,
  rpt strip_tac >>
  first_x_assum (qspecl_then [`cw`, `\v. T`, `X`] mp_tac) >>
  `(\v. (\v. T) v /\ X v) = X` by rw[FUN_EQ_THM] >>
  pop_assum SUBST1_TAC >>
  fs[OughtNow_def] >> metis_tac[]);

(* Knows is factive *)
val K1 = prove(``!A w. Knows A w ==> A w``, metis_tac[Knows_def, epi_refl]);

(* Better is irreflexive on a satisfiable statement *)
val B1 = prove(``!A w. (?v. A v) ==> ~Better A A w``,
  rw[Better_def] >> metis_tac[br_limit]);

val _ = (T2; T4; T6; P6; K1; B1; print "ALL DEONTIC TESTS PASSED\n");   (* only reached if every test above was proved *)
