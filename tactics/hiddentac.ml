(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Proof_type
open Tacmach

open Glob_term
open Refiner
open Genarg
open Tacexpr
open Tactics
open Util

(* Basic tactics *)
let h_intro_move x y =
  abstract_tactic (TacIntroMove (x, y)) (intro_move x y)
let h_intro x        = h_intro_move (Some x) no_move
let h_intros_until x = abstract_tactic (TacIntrosUntil x) (intros_until x)
let h_assumption     = abstract_tactic TacAssumption assumption
let h_exact c        = abstract_tactic (TacExact c) (exact_check c)
let h_exact_no_check c =
  abstract_tactic (TacExactNoCheck c) (exact_no_check c)
let h_vm_cast_no_check c =
  abstract_tactic (TacVmCastNoCheck c) (vm_cast_no_check c)
let h_apply simple ev cb =
  abstract_tactic (TacApply (simple,ev,List.map snd cb,None))
    (apply_with_bindings_gen simple ev cb)
let h_apply_in simple ev cb (id,ipat as inhyp) =
  abstract_tactic (TacApply (simple,ev,List.map snd cb,Some inhyp))
    (apply_in simple ev id cb ipat)
let h_elim ev cb cbo    =
  abstract_tactic (TacElim (ev,cb,cbo))
    (elim ev cb cbo)
let h_elim_type c    = abstract_tactic (TacElimType c) (elim_type c)
let h_case ev cb     = abstract_tactic (TacCase (ev,cb)) (general_case_analysis ev cb)
let h_case_type c    = abstract_tactic (TacCaseType c) (case_type c)
let h_fix ido n      = abstract_tactic (TacFix (ido,n)) (fix ido n)
let h_mutual_fix b id n l =
  abstract_tactic
    (TacMutualFix (b,id,n,l))
    (mutual_fix id n l 0)

let h_cofix ido      = abstract_tactic (TacCofix ido) (cofix ido)
let h_mutual_cofix b id l =
  abstract_tactic
    (TacMutualCofix (b,id,l))
    (mutual_cofix id l 0)

let h_cut c          = abstract_tactic (TacCut c) (cut c)
let h_generalize_gen cl =
  abstract_tactic (TacGeneralize cl)
    (generalize_gen (List.map (on_fst Redexpr.out_with_occurrences) cl))
let h_generalize cl =
  h_generalize_gen (List.map (fun c -> ((all_occurrences_expr,c),Names.Anonymous))
    cl)
let h_generalize_dep c =
  abstract_tactic (TacGeneralizeDep c) (generalize_dep c)
let h_let_tac b na c cl =
  let with_eq = if b then None else Some (true,(dummy_loc,IntroAnonymous)) in
  abstract_tactic (TacLetTac (na,c,cl,b)) (letin_tac with_eq na c None cl)
let h_let_pat_tac b na c cl =
  let with_eq = if b then None else Some (true,(dummy_loc,IntroAnonymous)) in
  abstract_tactic (TacLetTac (na,snd c,cl,b))
    (letin_pat_tac with_eq na c None cl)

(* Derived basic tactics *)
let h_simple_induction_destruct isrec h =
  abstract_tactic (TacSimpleInductionDestruct (isrec,h))
    (if isrec then (simple_induct h) else (simple_destruct h))
let h_simple_induction = h_simple_induction_destruct true
let h_simple_destruct = h_simple_induction_destruct false

let out_indarg = function
  | ElimOnConstr (_,c) -> ElimOnConstr c
  | ElimOnIdent id -> ElimOnIdent id
  | ElimOnAnonHyp n -> ElimOnAnonHyp n

let h_induction_destruct isrec ev lcl =
  let lcl' = on_fst (List.map (fun (a,b,c) ->(List.map out_indarg a,b,c))) lcl in
  abstract_tactic (TacInductionDestruct (isrec,ev,lcl'))
    (induction_destruct isrec ev lcl)
let h_new_induction ev c e idl cl =
  h_induction_destruct true ev ([c,e,idl],cl)
let h_new_destruct ev c e idl cl = h_induction_destruct false ev ([c,e,idl],cl)

let h_specialize n d = abstract_tactic (TacSpecialize (n,d)) (specialize n d)
let h_lapply c = abstract_tactic (TacLApply c) (cut_and_apply c)

(* Context management *)
let h_clear b l = abstract_tactic (TacClear (b,l))
  ((if b then keep else clear) l)
let h_clear_body l = abstract_tactic (TacClearBody l) (clear_body l)
let h_move dep id1 id2 =
  abstract_tactic (TacMove (dep,id1,id2)) (move_hyp dep id1 id2)
let h_rename l =
  abstract_tactic (TacRename l) (rename_hyp l)
let h_revert l = abstract_tactic (TacRevert l) (revert l)

(* Constructors *)
let h_left ev l  = abstract_tactic (TacLeft (ev,l)) (left_with_bindings ev l)
let h_right ev l = abstract_tactic (TacRight (ev,l)) (right_with_bindings ev l)
let h_split ev l = abstract_tactic (TacSplit (ev,false,l)) (split_with_bindings ev l)
(* Moved to tacinterp because of dependencies in Tacinterp.interp
let h_any_constructor t =
  abstract_tactic (TacAnyConstructor t) (any_constructor t)
*)
let h_constructor ev n l =
  abstract_tactic (TacConstructor(ev,ArgArg n,l))(constructor_tac ev None n l)
let h_one_constructor n =
  abstract_tactic (TacConstructor(false,ArgArg n,NoBindings)) (one_constructor n NoBindings)
let h_simplest_left   = h_left false NoBindings
let h_simplest_right  = h_right false NoBindings

(* Conversion *)
let h_reduce r cl  =
  abstract_tactic (TacReduce (r,cl)) (reduce r cl)
let h_change op c cl =
  abstract_tactic (TacChange (op,c,cl)) (change op c cl)

(* Equivalence relations *)
let h_reflexivity    = abstract_tactic TacReflexivity intros_reflexivity
let h_symmetry c     = abstract_tactic (TacSymmetry c) (intros_symmetry c)
let h_transitivity c =
  abstract_tactic (TacTransitivity c)
    (intros_transitivity c)

let h_simplest_apply c = h_apply false false [dummy_loc,(c,NoBindings)]
let h_simplest_eapply c = h_apply false true [dummy_loc,(c,NoBindings)]
let h_simplest_elim c   = h_elim false (c,NoBindings) None
let h_simplest_case   c = h_case false (c,NoBindings)

let h_intro_patterns l = abstract_tactic (TacIntroPattern l) (intro_patterns l)

