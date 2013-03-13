(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Evd
open Evarutil
open Evarsolve

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

let depends_on_evar evk _ (pbty,_,t1,t2) =
  try Int.equal (head_evar t1) evk
  with NoHeadEvar ->
  try Int.equal (head_evar t2) evk
  with NoHeadEvar -> false

let define_and_solve_constraints evk c evd =
  let evd = define evk c evd in
  let (evd,pbs) = extract_changed_conv_pbs evd (depends_on_evar evk) in
  match
    List.fold_left
      (fun p (pbty,env,t1,t2) -> match p with
	| Success evd -> Evarconv.evar_conv_x full_transparent_state env evd pbty t1 t2
	| UnifFailure _ as x -> x) (Success evd)
      pbs
  with
    | Success evd -> evd
    | UnifFailure _ -> error "Instance does not satisfy the constraints."

let w_refine (evk,evi) (ltac_var,rawc) sigma =
  if Evd.is_defined sigma evk then
    error "Instantiate called on already-defined evar";
  let env = Evd.evar_filtered_env evi in
  let sigma',typed_c =
    try Pretyping.understand_ltac ~resolve_classes:true true 
      sigma env ltac_var (Pretyping.OfType (Some evi.evar_concl)) rawc
    with e when Errors.noncritical e ->
      let loc = Glob_ops.loc_of_glob_constr rawc in
      user_err_loc
        (loc,"",Pp.str ("Instance is not well-typed in the environment of " ^
			string_of_existential evk))
  in
  define_and_solve_constraints evk typed_c (evars_reset_evd sigma' sigma)

(* vernac command Existential *)

(* Main component of vernac command Existential *)
let instantiate_pf_com evk com sigma =
  let evi = Evd.find sigma evk in
  let env = Evd.evar_filtered_env evi in
  let rawc = Constrintern.intern_constr sigma env com in
  let sigma' = w_refine (evk,evi) (([],[]),rawc) sigma in
  sigma'
