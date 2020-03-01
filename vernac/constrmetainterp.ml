(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Ltac_pretype
open Evd
open EConstr
open Environ
open Glob_term
open Pretyping
open Constrintern
open Patternops
open Geninterp

(**********************************************************************)
(* Interpreting constr containing variables of the metalanguage (e.g. Ltac) *)

module type ConstrCoercionSig =
sig
  val trace : (env -> evar_map -> ltac_var_map -> glob_constr -> evar_map * constr) ->
           interp_sign -> env -> evar_map -> ltac_var_map -> glob_constr -> evar_map * constr
  val coerce_to_uconstr : Val.t -> closed_glob_constr
  val coerce_to_constr : env -> Val.t -> constr_under_binders
  val coerce_to_constr_list : env -> Val.t -> constr list
  val coerce_var_to_ident : bool -> env -> evar_map -> Val.t -> Id.t
  val name : string
end

module Make (M : ConstrCoercionSig) =
struct

  (* Extract the uconstr list from lfun *)
  let extract_constr_context ist env sigma =
    let add_uconstr id v map =
      try Id.Map.add id (M.coerce_to_uconstr v) map
      with CannotCoerceTo _ -> map
    in
    let add_constr id v map =
      try Id.Map.add id (M.coerce_to_constr env v) map
      with CannotCoerceTo _ -> map
    in
    let add_ident id v map =
      try Id.Map.add id (M.coerce_var_to_ident false env sigma v) map
      with CannotCoerceTo _ -> map
    in
    let fold id v {idents;typed;untyped} =
      let idents = add_ident id v idents in
      let typed = add_constr id v typed in
      let untyped = add_uconstr id v untyped in
      { idents ; typed ; untyped }
    in
    let empty =  { idents = Id.Map.empty ;typed = Id.Map.empty ; untyped = Id.Map.empty } in
    Id.Map.fold fold ist.lfun empty

  (** Significantly simpler than [interp_constr], to interpret an
      untyped constr, it suffices to adjoin a closure environment. *)
  let interp_glob_closure ist env sigma ?(kind=WithoutTypeConstraint) ?(pattern_mode=false) (term,term_expr_opt) =
    let closure = extract_constr_context ist env sigma in
    match term_expr_opt with
    | None -> { closure ; term }
    | Some term_expr ->
       (* If at toplevel (term_expr_opt<>None), the error can be due to
         an incorrect context at globalization time: we retype with the
         now known intros/lettac/inversion hypothesis names *)
        let constr_context =
          Id.Set.union
            (Id.Map.domain closure.typed)
            (Id.Map.domain closure.untyped)
        in
        let ltacvars = {
          ltac_vars = constr_context;
          ltac_bound = Id.Map.domain ist.lfun;
          ltac_extra = Genintern.Store.empty;
        } in
        { closure ;
          term = Constrintern.for_grammar (intern_gen kind ~pattern_mode ~ltacvars env sigma) term_expr }

  let interp_gen kind ist pattern_mode flags env sigma c =
    let kind_for_intern = match kind with OfType _ -> WithoutTypeConstraint | _ -> kind in
    let { closure = constrvars ; term } =
      interp_glob_closure ist env sigma ~kind:kind_for_intern ~pattern_mode c in
    let vars = {
      ltac_constrs = constrvars.typed;
      ltac_uconstrs = constrvars.untyped;
      ltac_idents = constrvars.idents;
      ltac_genargs = ist.lfun;
    } in
    M.trace
      (fun env sigma vars -> understand_ltac flags env sigma vars kind) ist env sigma vars term

  let constr_flags () = {
    use_typeclasses = UseTC;
    solve_unification_constraints = true;
    fail_evar = true;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  }

  (* Interprets a constr; expects evars to be solved *)
  let interp_constr_gen kind ist env sigma c =
    let flags = { (constr_flags ()) with polymorphic = ist.Geninterp.poly } in
    interp_gen kind ist false flags env sigma c

  let interp_constr = interp_constr_gen WithoutTypeConstraint

  let interp_type = interp_constr_gen IsType

  let open_constr_use_classes_flags () = {
    use_typeclasses = UseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  }

  let open_constr_no_classes_flags () = {
    use_typeclasses = NoUseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  }

  let pure_open_constr_flags = {
    use_typeclasses = NoUseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = false;
    program_mode = false;
    polymorphic = false;
  }

  (* Interprets an open constr *)
  let interp_open_constr ?(expected_type=WithoutTypeConstraint) ?(flags=open_constr_no_classes_flags ()) ist env sigma c =
    interp_gen expected_type ist false flags env sigma c

  let interp_open_constr_with_classes ?(expected_type=WithoutTypeConstraint) ist env sigma c =
    interp_gen expected_type ist false (open_constr_use_classes_flags ()) env sigma c

  let interp_pure_open_constr ist =
    interp_gen WithoutTypeConstraint ist false pure_open_constr_flags

  let interp_typed_pattern ist env sigma (_,c,_) =
    let sigma, c =
      interp_gen WithoutTypeConstraint ist true pure_open_constr_flags env sigma c in
    (* FIXME: it is necessary to be unsafe here because of the way we handle
       evars in the pretyper. Sometimes they get solved eagerly. *)
    pattern_of_constr env sigma (EConstr.Unsafe.to_constr c)

  (* Interprets a list in which any element can be a list *)
  let interp_in_compound_list dest_fun coerce_fun interp_fun ist env sigma l =
    let try_expand_var sigma x =
      try match DAst.get (fst (dest_fun x)) with
      | GVar id ->
        let v = Id.Map.find id ist.lfun in
        sigma, coerce_fun env v
      | _ ->
          raise Not_found
      with CannotCoerceTo _ | Not_found ->
        (* dest_fun, List.assoc may raise Not_found *)
        let sigma, c = interp_fun ist env sigma x in
        sigma, [c] in
    let sigma, l = List.fold_left_map try_expand_var sigma l in
    sigma, List.flatten l

  let interp_constr_list ist env sigma c =
    interp_in_compound_list (fun x -> x)
      M.coerce_to_constr_list interp_constr ist env sigma c

  let interp_open_constr_list ist env sigma c =
    interp_in_compound_list (fun x -> x)
      M.coerce_to_constr_list interp_open_constr ist env sigma c

end
