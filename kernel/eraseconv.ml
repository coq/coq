(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Conversion

(** The erase evaluation function can either return an evaluated term or an error if the
    evaluated term cannot be read back *)
type erase_evaluation_function =
  Environ.env -> Constr.t -> types -> (Constr.t, unit) result

let erase_evaluation : erase_evaluation_function option ref = ref None

let install_erase_conv fn =
  match !erase_evaluation with
  | None -> erase_evaluation := Some fn
  | Some _ -> CErrors.anomaly Pp.(str"Attempting to install erasure evaluation twice!")

let evaluate_term env c ty =
  match !erase_evaluation with
  | None -> Result.Error ()
  | Some ev -> ev env c ty

let evaluate_args env ctx args =
  let open Context.Rel.Declaration in
  if Int.equal (Array.length args) 0 then args else
  let newargs = Array.make (Array.length args) args.(0) in
  let ctx = Vars.smash_rel_context ctx in
  let rec aux ctx n =
    match ctx with
    | LocalAssum (_, ty) :: ctx ->
      let arg' =
        match evaluate_term env args.(n) ty with
        | Result.Ok arg' -> arg'
        | Result.Error () -> args.(n)
      in
      newargs.(n) <- arg';
      (* ctx is a telescope (reverse context) *)
      aux (List.rev (Vars.subst1_rel_context arg' (List.rev ctx))) (succ n)
    | LocalDef _ :: _ -> assert false (* Context is smashed beforehand *)
    | [] -> ()
  in
  let () = aux (List.rev ctx) 0 in
  newargs

let erase_eval env expected_type =
  let hd, args = Constr.decompose_app expected_type in
  match Constr.kind hd with
  | Ind (ind, u) ->
    if Array.length args > 0 then
      let specif = (Inductive.lookup_mind_specif env ind, u) in
      let indty = Inductive.type_of_inductive specif in
      let paramsctxt = (fst (fst specif)).Declarations.mind_params_ctxt in
      let nparams = List.length paramsctxt in
      let ctx, concl = Term.decompose_prod_n_decls nparams indty in
      let params, indices = CArray.chop (fst (fst specif)).Declarations.mind_nparams args in
      let instconcl = Vars.(substl (subst_of_rel_context_instance ctx params) concl) in
      let indsctx, _ = Term.destArity instconcl in
      let indices' = evaluate_args env indsctx indices in
      let newty = Term.appvectc hd (Array.append params indices') in
      Result.Ok newty
    else Result.Error ()
  | _ -> Result.Error ()

let erase_conv pb env ty ty' =
  match erase_eval env ty' with
  | Result.Ok newty -> default_conv pb env ty newty
  | Result.Error () -> Result.Error ()
