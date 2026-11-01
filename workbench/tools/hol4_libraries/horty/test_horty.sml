(* Tests of hortyTheory. Each verdict is a theorem proved by EVAL; the final line prints only if all hold. *)
load "hortyTheory"; open hortyTheory;

(* Tweety: penguins are birds; birds fly (d1); penguins don't (d2); d2 is stronger *)
val tW = ``[Atom "P"; Impl (Atom "P") (Atom "B")]``;
val tD = ``[("d1", Atom "B", Atom "F"); ("d2", Atom "P", Neg (Atom "F"))]``;
val tP = ``[("d1", "d2")]``;
val tweety_scen = EVAL ``ProperScenarios ^tW ^tD ^tP``;
val tweety_req  = EQT_ELIM (EVAL ``RequiredH ^tW ^tD ^tP (Neg (Atom "F"))``);
val tweety_not  = EQF_ELIM (EVAL ``OughtH ^tW ^tD ^tP (Atom "F")``);

(* Nixon: Quaker (pacifist), Republican (not pacifist), no priority: two proper scenarios, a dilemma *)
val nW = ``[Atom "Q"; Atom "R"]``;
val nD = ``[("d1", Atom "Q", Atom "Pa"); ("d2", Atom "R", Neg (Atom "Pa"))]``;
val nixon_scen = EVAL ``ProperScenarios ^nW ^nD []``;
val nixon_both = EQT_ELIM (EVAL ``OughtH ^nW ^nD [] (Atom "Pa") /\ OughtH ^nW ^nD [] (Neg (Atom "Pa"))``);
val nixon_req  = EQF_ELIM (EVAL ``RequiredH ^nW ^nD [] (Atom "Pa")``);

(* Groundedness: a default that only supports itself is not proper *)
val ground_scen = EVAL ``ProperScenarios [] [("d1", Atom "A", Atom "A")] []``;

(* g02 by hand: three reasons; protecting the river is stronger than going along; pausing excludes bumping *)
val gW = ``[Atom "Misrep"; Atom "Job"; Atom "Ordered"; Impl (Atom "Pause") (Neg (Atom "Bump"))]``;
val gD = ``[("go_along", Atom "Ordered", Atom "Bump");
            ("protect_river", Atom "Misrep", Neg (Atom "Bump"));
            ("pause", Conj (Atom "Misrep") (Atom "Job"), Atom "Pause")]``;
val gP = ``[("go_along", "protect_river")]``;
val g02_scen = EVAL ``ProperScenarios ^gW ^gD ^gP``;
val g02_pause = EQT_ELIM (EVAL ``RequiredH ^gW ^gD ^gP (Atom "Pause")``);
val g02_nobump = EQF_ELIM (EVAL ``OughtH ^gW ^gD ^gP (Atom "Bump")``);
(* the same without the priority: going along is no longer defeated *)
val g02_nopri_scen = EVAL ``ProperScenarios ^gW ^gD []``;
val g02_nopri_bump = EQT_ELIM (EVAL ``OughtH ^gW ^gD [] (Atom "Bump")``);

val _ = (tweety_req; tweety_not; nixon_both; nixon_req; g02_pause; g02_nobump; g02_nopri_bump;
         print "ALL HORTY TESTS PASSED\n");
