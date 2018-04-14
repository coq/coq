(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Evd
open Evarutil
open Evarsolve
open Pp
open Glob_term
open Ltac_pretype

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

type glob_constr_ltac_closure = ltac_var_map * glob_constr

let depends_on_evar sigma evk _ (pbty,_,t1,t2) =
  try Evar.equal (head_evar sigma t1) evk
  with NoHeadEvar ->
  try Evar.equal (head_evar sigma t2) evk
  with NoHeadEvar -> false

let define_and_solve_constraints evk c env evd =
  if Termops.occur_evar evd evk c then
    Pretype_errors.error_occur_check env evd evk c;
  let evd = define evk c evd in
  let (evd,pbs) = extract_changed_conv_pbs evd (depends_on_evar evd evk) in
  match
    List.fold_left
      (fun p (pbty,env,t1,t2) -> match p with
        | Success evd -> Evarconv.evar_conv_x full_transparent_state env evd pbty t1 t2
	| UnifFailure _ as x -> x) (Success evd)
      pbs
  with
    | Success evd -> evd
    | UnifFailure _ -> user_err Pp.(str "Instance does not satisfy the constraints.")

let w_refine (evk,evi) (ltac_var,rawc) sigma =
  if Evd.is_defined sigma evk then
    user_err Pp.(str "Instantiate called on already-defined evar");
  let env = Evd.evar_filtered_env evi in
  let sigma',typed_c =
    let flags = {
      Pretyping.use_typeclasses = true;
      Pretyping.solve_unification_constraints = true;
      Pretyping.use_hook = None;
      Pretyping.fail_evar = false;
      Pretyping.expand_evars = true } in
    try Pretyping.understand_ltac flags
      env sigma ltac_var (Pretyping.OfType evi.evar_concl) rawc
    with e when CErrors.noncritical e ->
      let loc = Glob_ops.loc_of_glob_constr rawc in
      user_err ?loc 
                (str "Instance is not well-typed in the environment of " ++
                 Termops.pr_existential_key sigma evk ++ str ".")
  in
  define_and_solve_constraints evk typed_c env (evars_reset_evd sigma' sigma)
