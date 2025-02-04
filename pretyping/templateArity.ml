(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open EConstr

type template_binder = {
  bind_sort : Sorts.t;
  default : Sorts.t;
}

type template_arity =
  | NonTemplateArg of Name.t binder_annot * types * template_arity
  | TemplateArg of Name.t binder_annot * rel_context * template_binder * template_arity
  | DefParam of Name.t binder_annot * constr * types * template_arity
  | CtorType of Declarations.template_universes * types
  | IndType of Declarations.template_universes * rel_context * Sorts.t

let get_template_arity env ind ~ctoropt =
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let template = match mib.mind_template with
    | None -> assert false
    | Some t -> t
  in
  let type_after_params = match ctoropt with
    | None ->
      let ctx = List.rev @@ List.skipn (List.length mib.mind_params_ctxt) @@
        List.rev mip.mind_arity_ctxt
      in
      IndType (template, EConstr.of_rel_context ctx, template.template_concl)
    | Some ctor ->
      let ctyp = mip.mind_user_lc.(ctor-1) in
      let _, ctyp = Term.decompose_prod_n_decls (List.length mib.mind_params_ctxt) ctyp in
      (* don't bother with Prop for constructors *)
      CtorType (template, EConstr.of_constr ctyp)
  in
  let rec aux is_template (params:Constr.rel_context) = match is_template, params with
    | _, LocalDef (na,v,t) :: params ->
      let codom = aux is_template params in
      DefParam (EConstr.of_binder_annot na, EConstr.of_constr v, EConstr.of_constr t, codom)
    | [], [] -> type_after_params
    | _ :: _, [] | [], LocalAssum _ :: _ -> assert false
    | None :: is_template, LocalAssum (na,t) :: params ->
      let codom = aux is_template params in
      NonTemplateArg (EConstr.of_binder_annot na, EConstr.of_constr t, codom)
    | Some bind_sort :: is_template, LocalAssum (na,t) :: params ->
      let ctx, _ = Term.decompose_prod_decls t in
      let codom = aux is_template params in
      let default = UVars.subst_instance_sort template.template_defaults bind_sort in
      let binder = { bind_sort; default } in
      TemplateArg (EConstr.of_binder_annot na, EConstr.of_rel_context ctx, binder, codom)
  in
  let res = aux template.template_param_arguments (List.rev mib.mind_params_ctxt) in
  res
