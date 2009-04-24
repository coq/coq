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
open Pretyping

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

(* w_tactic pour instantiate *) 

let w_refine evk (ltac_vars,rawc) evd =
  if Evd.is_defined (evars_of evd) evk then 
    error "Instantiate called on already-defined evar";
  let e_info = Evd.find (evars_of evd) evk in
  let env = Evd.evar_env e_info in
  let evd',typed_c =
    try Pretyping.Default.understand_ltac 
      (evars_of evd) env ltac_vars (OfType (Some e_info.evar_concl)) rawc
    with _ ->
      let loc = Rawterm.loc_of_rawconstr rawc in
      user_err_loc 
        (loc,"",Pp.str ("Instance is not well-typed in the environment of " ^
			string_of_existential evk))
  in
    evar_define evk typed_c (evars_reset_evd (evars_of evd') evd)

(* vernac command Existential *)

let instantiate_pf_com n com pfts = 
  let gls = top_goal_of_pftreestate pfts in
  let sigma = gls.sigma in 
  let (evk,evi) = 
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
  let evd' = w_refine evk (([],[]),rawc) evd in
    change_constraints_pftreestate (evars_of evd') pfts
