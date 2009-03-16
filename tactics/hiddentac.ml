(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Proof_type
open Tacmach

open Rawterm
open Refiner
open Genarg
open Tacexpr
open Tactics
open Util

let inj_id id = (dummy_loc,id)
let inj_open c = (Evd.empty,c)
let inj_open_wb (c,b) = ((Evd.empty,c),b)
let inj_ia = function
  | ElimOnConstr c -> ElimOnConstr (inj_open_wb c)
  | ElimOnIdent id -> ElimOnIdent id
  | ElimOnAnonHyp n -> ElimOnAnonHyp n
let inj_occ (occ,c) = (occ,inj_open c)

(* Basic tactics *)
let h_intro_move x y =
  abstract_tactic (TacIntroMove (x, y)) (intro_move x y)
let h_intro x        = h_intro_move (Some x) no_move
let h_intros_until x = abstract_tactic (TacIntrosUntil x) (intros_until x)
let h_assumption     = abstract_tactic TacAssumption assumption
let h_exact c        = abstract_tactic (TacExact (inj_open c)) (exact_check c)
let h_exact_no_check c =
  abstract_tactic (TacExactNoCheck (inj_open c)) (exact_no_check c)
let h_vm_cast_no_check c = 
  abstract_tactic (TacVmCastNoCheck (inj_open c)) (vm_cast_no_check c)
let h_apply simple ev cb =
  abstract_tactic (TacApply (simple,ev,cb,None))
    (apply_with_ebindings_gen simple ev cb)
let h_apply_in simple ev cb (id,ipat as inhyp) =
  abstract_tactic (TacApply (simple,ev,cb,Some inhyp))
    (apply_in simple ev id cb ipat)
let h_elim ev cb cbo    =
  abstract_tactic (TacElim (ev,inj_open_wb cb,Option.map inj_open_wb cbo))
    (elim ev cb cbo)
let h_elim_type c    = abstract_tactic (TacElimType (inj_open c)) (elim_type c)
let h_case ev cb     = abstract_tactic (TacCase (ev,inj_open_wb cb)) (general_case_analysis ev cb)
let h_case_type c    = abstract_tactic (TacCaseType (inj_open c)) (case_type c)
let h_fix ido n      = abstract_tactic (TacFix (ido,n)) (fix ido n)
let h_mutual_fix b id n l =
  abstract_tactic
    (TacMutualFix (b,id,n,List.map (fun (id,n,c) -> (id,n,inj_open c)) l))
    (mutual_fix id n l)

let h_cofix ido      = abstract_tactic (TacCofix ido) (cofix ido)
let h_mutual_cofix b id l =
  abstract_tactic
    (TacMutualCofix (b,id,List.map (fun (id,c) -> (id,inj_open c)) l)) 
    (mutual_cofix id l)

let h_cut c          = abstract_tactic (TacCut (inj_open c)) (cut c)
let h_generalize_gen cl =
  abstract_tactic (TacGeneralize (List.map (on_fst inj_occ) cl))
    (generalize_gen (List.map (on_fst Redexpr.out_with_occurrences) cl))
let h_generalize cl =
  h_generalize_gen (List.map (fun c -> ((all_occurrences_expr,c),Names.Anonymous))
    cl)
let h_generalize_dep c =
  abstract_tactic (TacGeneralizeDep (inj_open c))(generalize_dep c)
let h_let_tac b na c cl =
  let with_eq = if b then None else Some (true,(dummy_loc,IntroAnonymous)) in
  abstract_tactic (TacLetTac (na,inj_open c,cl,b)) (letin_tac with_eq na c None cl)
let h_instantiate n c ido = 
(Evar_tactics.instantiate n c ido)
  (* abstract_tactic (TacInstantiate (n,c,cls))
    (Evar_refiner.instantiate n c (goal_location_of cls)) *)

(* Derived basic tactics *)
let h_simple_induction_destruct isrec h =
  abstract_tactic (TacSimpleInductionDestruct (isrec,h)) 
    (if isrec then (simple_induct h) else (simple_destruct h))
let h_simple_induction = h_simple_induction_destruct true
let h_simple_destruct = h_simple_induction_destruct false

let h_induction_destruct isrec ev l =
  abstract_tactic (TacInductionDestruct (isrec,ev,List.map (fun (c,e,idl,cl) -> 
    List.map inj_ia c,Option.map inj_open_wb e,idl,cl) l))
    (induction_destruct ev isrec l)
let h_new_induction ev c e idl cl = h_induction_destruct ev true [c,e,idl,cl]
let h_new_destruct ev c e idl cl = h_induction_destruct ev false [c,e,idl,cl]

let h_specialize n d = abstract_tactic (TacSpecialize (n,inj_open_wb d)) (specialize n d)
let h_lapply c = abstract_tactic (TacLApply (inj_open c)) (cut_and_apply c)

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
let h_left ev l  = abstract_tactic (TacLeft (ev,l)) (left_with_ebindings ev l)
let h_right ev l = abstract_tactic (TacLeft (ev,l)) (right_with_ebindings ev l)
let h_split ev l = abstract_tactic (TacSplit (ev,false,l)) (split_with_ebindings ev l)
(* Moved to tacinterp because of dependencies in Tacinterp.interp
let h_any_constructor t =
  abstract_tactic (TacAnyConstructor t) (any_constructor t)
*)
let h_constructor ev n l =
  abstract_tactic (TacConstructor(ev,AI n,l))(constructor_tac ev None n l)
let h_one_constructor n = h_constructor false n NoBindings
let h_simplest_left   = h_left false NoBindings
let h_simplest_right  = h_right false NoBindings

(* Conversion *)
let h_reduce r cl  = 
  abstract_tactic (TacReduce (inj_red_expr r,cl)) (reduce r cl)
let h_change oc c cl =
  abstract_tactic (TacChange (Option.map inj_occ oc,inj_open c,cl))
    (change (Option.map Redexpr.out_with_occurrences oc) c cl)

(* Equivalence relations *)
let h_reflexivity    = abstract_tactic TacReflexivity intros_reflexivity
let h_symmetry c     = abstract_tactic (TacSymmetry c) (intros_symmetry c)
let h_transitivity c =
  abstract_tactic (TacTransitivity (inj_open c)) (intros_transitivity c)

let h_simplest_apply c  = h_apply false false [inj_open c,NoBindings]
let h_simplest_eapply c = h_apply false true [inj_open c,NoBindings]
let h_simplest_elim c   = h_elim false (c,NoBindings) None
let h_simplest_case   c = h_case false (c,NoBindings)

let h_intro_patterns l = abstract_tactic (TacIntroPattern l) (intro_patterns l)

