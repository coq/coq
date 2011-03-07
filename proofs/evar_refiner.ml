(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Evd
open Evarutil
open Sign
open Refiner

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

let depends_on_evar evk _ (pbty,_,t1,t2) =
  try head_evar t1 = evk
  with NoHeadEvar ->
  try head_evar t2 = evk
  with NoHeadEvar -> false

let define_and_solve_constraints evk c evd =
  try
    let evd = define evk c evd in
    let (evd,pbs) = extract_changed_conv_pbs evd (depends_on_evar evk) in
    fst (List.fold_left
      (fun (evd,b as p) (pbty,env,t1,t2) ->
	if b then Evarconv.evar_conv_x full_transparent_state env evd pbty t1 t2 else p) (evd,true)
      pbs)
  with e when Pretype_errors.precatchable_exception e ->
    error "Instance does not satisfy constraints."

let w_refine (evk,evi) (ltac_var,rawc) sigma =
  if Evd.is_defined sigma evk then
    error "Instantiate called on already-defined evar";
  let env = Evd.evar_env evi in
  let sigma',typed_c =
    try Pretyping.Default.understand_ltac true sigma env ltac_var
	  (Pretyping.OfType (Some evi.evar_concl)) rawc
    with _ ->
      let loc = Glob_term.loc_of_glob_constr rawc in
      user_err_loc
        (loc,"",Pp.str ("Instance is not well-typed in the environment of " ^
			string_of_existential evk))
  in
  define_and_solve_constraints evk typed_c (evars_reset_evd sigma' sigma)

(* vernac command Existential *)

(* Main component of vernac command Existential *)
let instantiate_pf_com evk com sigma =
  let evi = Evd.find sigma evk in
  let env = Evd.evar_env evi in
  let rawc = Constrintern.intern_constr sigma env com in
  let sigma' = w_refine (evk,evi) (([],[]),rawc) sigma in
  sigma'
