(* Shared by the checkers: decide "does g follow from these theorems?" fast and exactly where possible.
   Quantifiers over bool or over a type with finitely many plain constructors become one case per value; every
   statement that is not built from not, and, or, if, iff becomes a letter; HOL4's SAT solver then decides.
   Anything else (numbers, other types) is left to metis (5 s) and to rewriting with arithmetic. *)
val _ = (load "HolSatLib") handle _ => ();
(* A statement about a true-or-false argument is fixed by its value at T and at F: f a = (a /\ f T) \/ (~a /\ f F).
   HOL is extensional, so "Knows p" and "Knows q" are the same claim whenever p and q have the same truth value. The
   letters below treat each statement as independent; rewriting such statements first lets them see this. *)
fun debool t =
  if aconv t T orelse aconv t F then t
  else if is_neg t then mk_neg (debool (dest_neg t))
  else if is_conj t then let val (a, b) = dest_conj t in mk_conj (debool a, debool b) end
  else if is_disj t then let val (a, b) = dest_disj t in mk_disj (debool a, debool b) end
  else if is_imp_only t then let val (a, b) = dest_imp_only t in mk_imp (debool a, debool b) end
  else if is_eq t andalso type_of (lhs t) = bool then mk_eq (debool (lhs t), debool (rhs t))
  else if type_of t <> bool orelse is_forall t orelse is_exists t orelse is_abs t then t
  else
    let val (f, args) = strip_comb t
    in case List.find (fn a => type_of a = bool andalso not (aconv a T) andalso not (aconv a F)) args of
         NONE => t
       | SOME a =>
           let fun at v = list_mk_comb (f, map (fn x => if aconv x a then v else x) args)
               val da = debool a
           in mk_disj (mk_conj (da, debool (at T)), mk_conj (mk_neg da, debool (at F))) end
    end;

local
  fun finite_values ty =
    if ty = bool then SOME [T, F]
    else let val cs = TypeBase.constructors_of ty
         in if not (null cs) andalso List.all (fn k => type_of k = ty) cs then SOME cs else NONE end
         handle _ => NONE
  fun expand t =
    if is_forall t then
      let val (v, b) = dest_forall t
      in case finite_values (type_of v) of
           SOME vals => list_mk_conj (map (fn k => expand (subst [v |-> k] b)) vals)
         | NONE => t end
    else if is_exists t then
      let val (v, b) = dest_exists t
      in case finite_values (type_of v) of
           SOME vals => list_mk_disj (map (fn k => expand (subst [v |-> k] b)) vals)
         | NONE => t end
    else if is_neg t then mk_neg (expand (dest_neg t))
    else if is_conj t then let val (a, b) = dest_conj t in mk_conj (expand a, expand b) end
    else if is_disj t then let val (a, b) = dest_disj t in mk_disj (expand a, expand b) end
    else if is_imp_only t then let val (a, b) = dest_imp_only t in mk_imp (expand a, expand b) end
    else if is_eq t andalso type_of (lhs t) = bool then mk_eq (expand (lhs t), expand (rhs t))
    else t
  fun simp t = rhs (concl (SIMP_CONV (srw_ss ()) [] t)) handle _ => t   (* constructor facts: BumpFeed = X is F *)
  fun letters t =
    let val table = ref ([] : (term * term) list)
        fun letter x = case List.find (fn (a, _) => aconv a x) (!table) of
                         SOME (_, v) => v
                       | NONE => let val v = genvar bool in table := (x, v) :: !table; v end
        fun abs x =
          if aconv x T orelse aconv x F then x
          else if is_neg x then mk_neg (abs (dest_neg x))
          else if is_conj x then let val (a, b) = dest_conj x in mk_conj (abs a, abs b) end
          else if is_disj x then let val (a, b) = dest_disj x in mk_disj (abs a, abs b) end
          else if is_imp_only x then let val (a, b) = dest_imp_only x in mk_imp (abs a, abs b) end
          else if is_eq x andalso type_of (lhs x) = bool then mk_eq (abs (lhs x), abs (rhs x))
          else letter x
    in abs t end
  (* Quantifiers over an open type (one with no list of constructors, such as a type of eventualities) cannot be
     expanded into cases. They are instantiated with the type's ground terms that occur in the formula (its constants
     and free variables; one arbitrary element if there are none). Only replacements that keep soundness are made:
     a "for all" in the premises becomes the conjunction of its instances, a "there is" in the conclusion becomes the
     disjunction of its instances, so whatever SAT proves from the result really follows (Herbrand). *)
  fun is_open ty = ty <> bool andalso not (can dom_rng ty) andalso
                   (case finite_values ty of NONE => true | SOME _ => false) andalso ty <> numSyntax.num
  fun grounds ty t = Lib.op_mk_set aconv (List.filter (fn x => type_of x = ty) (free_vars t) @
                                          find_terms (fn x => is_const x andalso type_of x = ty) t)
  exception TooMany
  val instances_made = ref 0
  val instance_limit = 3000      (* past this, the formula is left as it is: SAT stays approximate, metis decides *)
  fun hb ctx pol t =
    let fun inst v b mk =
          case List.find (fn (ty, _) => ty = type_of v) ctx of
            SOME (_, cs) => (instances_made := !instances_made + length cs;
                             if !instances_made > instance_limit then raise TooMany else ();
                             mk (map (fn c => hb ctx pol (subst [v |-> c] b)) cs))
          | NONE => t
    in if is_neg t then mk_neg (hb ctx (not pol) (dest_neg t))
       else if is_conj t then let val (a, b) = dest_conj t in mk_conj (hb ctx pol a, hb ctx pol b) end
       else if is_disj t then let val (a, b) = dest_disj t in mk_disj (hb ctx pol a, hb ctx pol b) end
       else if is_imp_only t then let val (a, b) = dest_imp_only t in mk_imp (hb ctx (not pol) a, hb ctx pol b) end
       else if is_eq t andalso type_of (lhs t) = bool andalso
               can (find_term (fn x => is_forall x orelse is_exists x)) t then
         (* an "if and only if" holding a quantifier: both directions, so each side gets its polarity *)
         let val (a, b) = (lhs t, rhs t) in hb ctx pol (mk_conj (mk_imp (a, b), mk_imp (b, a))) end
       else if is_forall t andalso not pol then let val (v, b) = dest_forall t in inst v b list_mk_conj end
       else if is_exists t andalso pol then let val (v, b) = dest_exists t in inst v b list_mk_disj end
       else t end
  fun herbrand t =
    let val qs = find_terms (fn x => is_forall x orelse is_exists x) t
        val tys = Lib.mk_set (List.filter is_open (map (fn q => type_of (fst (if is_forall q then dest_forall q else dest_exists q))) qs))
        val ctx = map (fn ty => (ty, case grounds ty t of [] => [genvar ty] | cs => cs)) tys
    in if null ctx then t else (instances_made := 0; hb ctx true t handle TooMany => t) end
  (* the SAT answer is exact when nothing the letters cannot see is left: no quantifier, no lambda, no number, no
     equation between non-truth values, and every term of an open type a constant or a variable *)
  fun exact t =
    not (can (find_term (fn x => is_forall x orelse is_exists x orelse is_abs x)) t) andalso
    not (can (find_term (fn x => is_eq x andalso type_of (lhs x) <> bool)) t) andalso
    not (can (find_term (fn x => type_of x = numSyntax.num)) t) andalso
    List.all (fn x => is_const x orelse is_var x) (find_terms (fn x => is_open (type_of x)) t)
  val expand_finite_quantifiers = expand
  fun sat_valid t = (HolSatLib.SAT_PROVE t; true) handle _ => ((tautLib.TAUT_PROVE t; true) handle _ => false)
  val extra = [DISJ_IMP_THM, FORALL_AND_THM]
in
  val expand_finite = expand_finite_quantifiers
  val herbrand_instances = herbrand
  (* SOME true: follows (proved by SAT); SOME false: does not follow (exact case only); NONE: SAT cannot settle it *)
  fun prop_decide ths g =
    let val hyps = map (fn th => debool (simp (expand (concl th)))) ths
        val goal = debool (simp (expand g))
        val phi = herbrand (if null hyps then goal else mk_imp (list_mk_conj hyps, goal))
    in if sat_valid (letters phi) then SOME true else if exact phi then SOME false else NONE end
    handle _ => NONE
  fun prop_follows ths g = (prop_decide ths g = SOME true)
  fun slow_follows ths g =
    ((metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ();
     ((TAC_PROOF (([], g), rpt strip_tac >> metis_tac ths); true) handle _ => false) orelse
     ((TAC_PROOF (([], g), rw (ths @ extra) >> rpt decide_tac); true) handle _ => false))
  fun follows_fast ths g = prop_follows ths g orelse slow_follows ths g
end;

(* Split "premises ==> c1 /\ ... /\ cn" into one goal per conclusion, and decide each the cheapest way that works:
   the SAT check, then rewriting with arithmetic, then metis (5 s). *)
local
  val extra = [DISJ_IMP_THM, FORALL_AND_THM]
  fun split_goal g =
    let val (vs, b) = strip_forall g
    in if is_imp_only b then
         let val (a, c) = dest_imp_only b in map (fn ci => list_mk_forall (vs, mk_imp (a, ci))) (strip_conj c) end
       else map (fn ci => list_mk_forall (vs, ci)) (strip_conj b) end
  fun by_rw_decide asms ths g =
    ((metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ();
     (TAC_PROOF ((map concl asms, g),
        rw (ths @ extra) >> rpt (FIRST [decide_tac, metis_tac (asms @ ths @ [arithmeticTheory.LESS_ANTISYM])])); true)
     handle _ => false)
  fun by_metis5 asms ths g =
    ((metisTools.limit := {time = SOME 5.0, infs = NONE}) handle _ => ();
     (TAC_PROOF ((map concl asms, g), rpt strip_tac >> metis_tac (asms @ ths)); true) handle _ => false)
in
  fun follows_each asms ths g =
    List.all (fn gi => case prop_decide (asms @ ths) gi of
                         SOME b => b
                       | NONE => by_rw_decide asms ths gi orelse by_metis5 asms ths gi)
             (split_goal g)
end;

(* Every smallest set of items from pool that gives g, found by dualization: a smallest set not found yet misses some
   smallest hitting set of the found ones, so testing the complement of every such hitting set finds it, and when every
   test fails the list is complete. "gives items g" decides whether the items give g. Returns (sets, complete). *)
local
  fun mem x l = List.exists (fn y => y = x) l
  fun minus a b = List.filter (fn x => not (mem x b)) a
  fun subset a b = List.all (fn x => mem x b) a
  fun same a b = subset a b andalso subset b a
  fun add_set hs m =
    let val grown = List.concat (map (fn h => if List.exists (fn x => mem x m) h then [h] else map (fn x => x :: h) m) hs)
        val smallest = List.filter (fn h => not (List.exists (fn h' => subset h' h andalso not (same h' h)) grown)) grown
    in List.foldl (fn (h, acc) => if List.exists (same h) acc then acc else h :: acc) [] smallest end
  fun hitting ms = List.foldl (fn (m, hs) => add_set hs m) [[]] ms
in
  fun shrink_by gives items g = List.foldl (fn (x, keep) =>
      let val rest = minus keep [x] in if gives rest g then rest else keep end) items items
  fun all_smallest gives pool g =
    if not (gives pool g) then ([], true)
    else let
      fun loop ms =
        let val hs = hitting ms
        in if length hs > 2000 then (ms, false)
           else case List.find (fn h => gives (minus pool h) g) hs of
                  NONE => (ms, true)
                | SOME h => loop (shrink_by gives (minus pool h) g :: ms) end
    in loop [shrink_by gives pool g] end
end;
