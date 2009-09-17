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

let w_refine (evk,evi) (ltac_var,rawc) sigma =
  if Evd.is_defined sigma evk then
    error "Instantiate called on already-defined evar";
  let env = Evd.evar_env evi in
  let sigma',typed_c =
    try Pretyping.Default.understand_ltac sigma env ltac_var
	  (Pretyping.OfType (Some evi.evar_concl)) rawc
    with _ ->
      let loc = Rawterm.loc_of_rawconstr rawc in
      user_err_loc
        (loc,"",Pp.str ("Instance is not well-typed in the environment of " ^
			string_of_existential evk))
  in
    define evk typed_c (evars_reset_evd sigma' sigma)

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
  let sigma' = w_refine (evk,evi) (([],[]),rawc) sigma in
  change_constraints_pftreestate sigma' pfts
