(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Proof_type
open Tacmach

open Rawterm
open Refiner
open Tacexpr
open Tactics
open Util

let inj_id id = (dummy_loc,id)

(* Basic tactics *)
let h_intro_move x y =
  abstract_tactic (TacIntroMove (x, option_app inj_id y)) (intro_move x y)
let h_intro x        = h_intro_move (Some x) None
let h_intros_until x = abstract_tactic (TacIntrosUntil x) (intros_until x)
let h_assumption     = abstract_tactic TacAssumption assumption
let h_exact c        = abstract_tactic (TacExact c) (exact_check c)
let h_apply cb       = abstract_tactic (TacApply cb) (apply_with_bindings cb)
let h_elim cb cbo    = abstract_tactic (TacElim (cb,cbo)) (elim cb cbo)
let h_elim_type c    = abstract_tactic (TacElimType c) (elim_type c)
let h_case cb        = abstract_tactic (TacCase cb) (general_case_analysis cb)
let h_case_type c    = abstract_tactic (TacCaseType c) (case_type c)
let h_fix ido n      = abstract_tactic (TacFix (ido,n)) (fix ido n)
let h_mutual_fix id n l =
  abstract_tactic (TacMutualFix (id,n,l)) (mutual_fix id n l)
let h_cofix ido      = abstract_tactic (TacCofix ido) (cofix ido)
let h_mutual_cofix id l =
  abstract_tactic (TacMutualCofix (id,l)) (mutual_cofix id l)

let h_cut c          = abstract_tactic (TacCut c) (cut c)
let h_true_cut ido c = abstract_tactic (TacTrueCut (ido,c)) (true_cut ido c)
let h_forward b na c = abstract_tactic (TacForward (b,na,c)) (forward b na c)
let h_generalize cl  = abstract_tactic (TacGeneralize cl) (generalize cl)
let h_generalize_dep c = abstract_tactic (TacGeneralizeDep c)(generalize_dep c)
let h_let_tac id c cl =
  abstract_tactic (TacLetTac (id,c,cl)) (letin_tac true (Names.Name id) c cl)
let h_instantiate n c = 
  abstract_tactic (TacInstantiate (n,c)) (Evar_refiner.instantiate n c)

(* Derived basic tactics *)
let h_old_induction h = abstract_tactic (TacOldInduction h) (old_induct h)
let h_old_destruct h  = abstract_tactic (TacOldDestruct h) (old_destruct h)
let h_new_induction c = abstract_tactic (TacNewInduction c) (new_induct c)
let h_new_destruct c = abstract_tactic (TacNewDestruct c) (new_destruct c)
let h_specialize n (c,bl as d) =
  abstract_tactic (TacSpecialize (n,d)) (new_hyp n c bl)
let h_lapply c = abstract_tactic (TacLApply c) (cut_and_apply c)

(* Context management *)
let inj x = AN (Rawterm.dummy_loc,x)
let h_clear l = abstract_tactic (TacClear (List.map inj l)) (clear l)
let h_clear_body l =
  abstract_tactic (TacClearBody (List.map inj l)) (clear_body l)
let h_move dep id1 id2 =
  abstract_tactic (TacMove (dep,inj_id id1,inj_id id2)) (move_hyp dep id1 id2)
let h_rename id1 id2 =
  abstract_tactic (TacRename (inj_id id1,inj_id id2)) (rename_hyp id1 id2)

(* Constructors *)
let h_left l          = abstract_tactic (TacLeft l) (left l)
let h_right l         = abstract_tactic (TacLeft l) (right l)
let h_split l         = abstract_tactic (TacSplit l) (split l)
(* Moved to tacinterp because of dependence in Tacinterp.interp
let h_any_constructor t =
  abstract_tactic (TacAnyConstructor t) (any_constructor t)
*)
let h_constructor n l =
  abstract_tactic (TacConstructor(AI n,l))(constructor_tac None n l)
let h_one_constructor n = h_constructor n NoBindings
let h_simplest_left   = h_left NoBindings
let h_simplest_right  = h_right NoBindings

(* Conversion *)
let h_reduce r cl  = abstract_tactic (TacReduce (r,cl)) (reduce r cl)
let h_change c cl  = abstract_tactic (TacChange (c,cl)) (change c cl)

(* Equivalence relations *)
let h_reflexivity    = abstract_tactic TacReflexivity intros_reflexivity
let h_symmetry       = abstract_tactic TacSymmetry intros_symmetry
let h_transitivity c =
  abstract_tactic (TacTransitivity c) (intros_transitivity c)

(*
let h_clear ids         = v_clear  [(Clause (List.map (fun x -> InHyp x) ids))]
let h_move dep id1 id2  = 
 (if dep then v_move else v_move_dep) [Identifier id1;Identifier id2]
let h_reflexivity       = v_reflexivity   []
let h_symmetry          = v_symmetry      []
let h_one_constructor i = v_constructor [(Integer i)]
let h_any_constructor   = v_constructor []
let h_transitivity c    = v_transitivity [(Constr c)]
let h_simplest_left     = v_left [(Cbindings [])]
let h_simplest_right    = v_right [(Cbindings [])]
let h_split     c       = v_split [(Constr c);(Cbindings [])]
*)

let h_simplest_apply c  = h_apply (c,NoBindings)
let h_simplest_elim c   = h_elim (c,NoBindings) None
(*
let h_inductionInt  i   = v_induction[(Integer i)]
let h_inductionId   id  = v_induction[(Identifier id)]
*)
let h_simplest_case   c = h_case (c,NoBindings)
(*
let h_destructInt  i    = v_destruct [(Integer i)]
let h_destructId   id   = v_destruct [(Identifier id)]
*)

