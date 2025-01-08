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

type template_arity =
  | NonTemplateArg of Name.t binder_annot * types * template_arity
  | TemplateArg of Name.t binder_annot * rel_context * Univ.Level.t * template_arity
  | DefParam of Name.t binder_annot * constr * types * template_arity
  | CtorType of Declarations.template_universes * types
  | IndType of Declarations.template_universes * rel_context * Sorts.t

(* be Prop if all these levels are Prop *)
type template_can_be_prop = { template_can_be_prop : Univ.Level.Set.t option }

let get_template_arity env ind ~ctoropt =
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let template = match mib.mind_template with
    | None -> assert false
    | Some t -> t
  in
  let can_be_prop, type_after_params = match ctoropt with
    | None ->
      let s = match mip.mind_arity with
        | RegularArity _ -> assert false
        | TemplateArity { template_level = s } -> s
      in
      let ctx = List.rev @@ List.skipn (List.length mib.mind_params_ctxt) @@
        List.rev mip.mind_arity_ctxt
      in
      let template_can_be_prop = match s with
        | SProp | Prop | Set -> None
        | QSort _ -> assert false
        | Type u ->
          (* if all template levels are instantiated to Prop, do we get Prop? *)
          let template_levels = Univ.ContextSet.levels template.template_context in
          if List.exists (fun (u,n) -> n > 0 || not (Univ.Level.Set.mem u template_levels))
              (Univ.Universe.repr u)
          then None
          else
            (* don't use the qvar for non used univs
               eg with "Ind (A:Type@{u}) (B:Type@{v}) : Type@{u}"
               "Ind True nat" should be Prop *)
            let used_template_levels =
              Univ.Level.Set.inter template_levels (Univ.Universe.levels u)
            in
            Some used_template_levels
      in
      { template_can_be_prop }, IndType (template, EConstr.of_rel_context ctx, s)
    | Some ctor ->
      let ctyp = mip.mind_user_lc.(ctor-1) in
      let _, ctyp = Term.decompose_prod_n_decls (List.length mib.mind_params_ctxt) ctyp in
      (* don't bother with Prop for constructors *)
      { template_can_be_prop = None}, CtorType (template, EConstr.of_constr ctyp)
  in
  let rec aux is_template (params:Constr.rel_context) = match is_template, params with
    | _, LocalDef (na,v,t) :: params ->
      let codom = aux is_template params in
      DefParam (EConstr.of_binder_annot na, EConstr.of_constr v, EConstr.of_constr t, codom)
    | [], [] -> type_after_params
    | _ :: _, [] | [], LocalAssum _ :: _ -> assert false
    | false :: is_template, LocalAssum (na,t) :: params ->
      let codom = aux is_template params in
      NonTemplateArg (EConstr.of_binder_annot na, EConstr.of_constr t, codom)
    | true :: is_template, LocalAssum (na,t) :: params ->
      let ctx, c = Term.decompose_prod_decls t in
      let u = match Constr.kind c with
        | Sort (Type u) -> begin match Univ.Universe.level u with
            | Some u -> u
            | None -> assert false
          end
        | _ -> assert false
      in
      let codom = aux is_template params in
      TemplateArg (EConstr.of_binder_annot na, EConstr.of_rel_context ctx, u, codom)
  in
  let res = aux template.template_param_arguments (List.rev mib.mind_params_ctxt) in
  can_be_prop, res
