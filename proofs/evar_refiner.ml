(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Evd
open Sign
open Proof_trees
open Refiner

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

(* w_tactic pour instantiate *) 

let w_refine ev rawc evd =
  if Evd.is_defined (evars_of evd) ev then 
    error "Instantiate called on already-defined evar";
  let e_info = Evd.find (evars_of evd) ev in
  let env = Evd.evar_env e_info in
  let sigma,typed_c = 
    try Pretyping.Default.understand_tcc (evars_of evd) env 
      ~expected_type:e_info.evar_concl rawc 
    with _ -> error ("The term is not well-typed in the environment of " ^
			string_of_existential ev)
  in
    evar_define ev typed_c (evars_reset_evd sigma evd)

(* vernac command Existential *)

let instantiate_pf_com n com pfts = 
  let gls = top_goal_of_pftreestate pfts in
  let sigma = gls.sigma in 
  let (sp,evi) (* as evc *) = 
    let evl = Evarutil.non_instantiated sigma in
      if (n <= 0) then
	error "incorrect existential variable index"
      else if List.length evl < n then
	  error "not so many uninstantiated existential variables"
      else
	List.nth evl (n-1)
  in 
  let env = Evd.evar_env evi in
  let rawc = Constrintern.intern_constr sigma env com in 
  let evd = create_goal_evar_defs sigma in
  let evd' = w_refine sp rawc evd in
    change_constraints_pftreestate (evars_of evd') pfts
