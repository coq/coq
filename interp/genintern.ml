(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg

module Store = Store.Make ()

type ntnvar_status = {
  mutable ntnvar_used : bool list;
  mutable ntnvar_used_as_binder : bool;
  mutable ntnvar_scopes : Notation_term.subscopes option;
  mutable ntnvar_binding_ids : Notation_term.notation_var_binders option;
  mutable ntnvar_is_only_in_constr: bool;
  ntnvar_typ : Notation_term.notation_var_internalization_type;
}

type intern_variable_status = {
  intern_ids : Id.Set.t;
  intern_univs : UnivNames.universe_binders;
  notation_variable_status : ntnvar_status Id.Map.t;
}

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Store.t;
  intern_sign : intern_variable_status;
  strict_check : bool;
}

let empty_intern_sign univs = {
  intern_ids = Id.Set.empty;
  intern_univs = univs;
  notation_variable_status = Id.Map.empty;
}

let empty_glob_sign ~strict env univs = {
  ltacvars = Id.Set.empty;
  genv = env;
  extra = Store.empty;
  intern_sign = empty_intern_sign univs;
  strict_check = strict;
}

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * Constrexpr.constr_expr option
type glob_constr_pattern_and_expr = Id.Set.t * glob_constr_and_expr * Pattern.uninstantiated_pattern

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
type 'glb ntn_subst_fun = ntnvar_status Id.Map.t -> (Id.t -> Glob_term.glob_constr option) -> 'glb -> 'glb

module InternObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb) intern_fun
  let name = "intern"
  let default _ = None
end

type ('raw, 'glb) constr_intern_fun = ?loc:Loc.t -> glob_sign -> 'raw -> 'glb

type constr_intern_info = { passthrough_impls : bool }

let default_info = { passthrough_impls = false }

let wrap_constr_intern (type raw glb) (tag:(raw,glb) GenConstr.tag) (f:(raw, glb) constr_intern_fun)
  : (raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun =
  fun ?loc ist v ->
  let v = f ?loc ist v in
  DAst.make ?loc @@ Glob_term.GGenarg (Glb (tag, v)), default_info

module CInternObj = struct
  type ('r, _) t = ('r, Glob_term.glob_constr * constr_intern_info) constr_intern_fun
end

module NtnSubstObj =
struct
  type (_, 'glb) t = 'glb ntn_subst_fun
end

module Intern = Register (InternObj)
module CIntern = GenConstr.Register (CInternObj)
module NtnSubst = GenConstr.Register (NtnSubstObj)

let intern = Intern.obj
let register_intern0 = Intern.register0
let register_intern_constr_gen = CIntern.register
let register_intern_constr tag f =
  register_intern_constr_gen tag (wrap_constr_intern tag f)

let generic_intern ist (GenArg (Rawwit wit, v)) =
  let (ist, v) = intern wit ist v in
  (ist, in_gen (glbwit wit) v)

let generic_intern_constr ?loc ist (GenConstr.Raw (tag, v)) =
  let internf = CIntern.get tag in
  internf ?loc ist v

module InternPatObj = struct
  type ('raw, _) t = ('raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun
end

module InternPat = GenConstr.Register (InternPatObj)

let register_intern_pat_gen = InternPat.register
let register_intern_pat tag f = register_intern_pat_gen tag (wrap_constr_intern tag f)

let generic_intern_pat ?loc ist (GenConstr.Raw (tag, v)) =
  match InternPat.find_opt tag with
  | None ->
    let name = GenConstr.repr tag in
    CErrors.user_err ?loc Pp.(str "This quotation is not supported in tactic patterns (" ++ str name ++ str ").")
  | Some internf ->
    let v = internf ?loc ist v in
    v

(** Notation substitution *)

let substitute_notation = NtnSubst.get
let register_ntn_subst0 = NtnSubst.register

let generic_substitute_notation avoid env (GenConstr.Glb (tag, v) as orig) =
  let v' = substitute_notation tag avoid env v in
  if v' == v then orig else Glb (tag, v')

let with_used_ntnvars ntnvars f =
  let () = Id.Map.iter (fun _ status ->
      status.ntnvar_used <- false:: status.ntnvar_used)
      ntnvars
  in
  match f () with
  | v ->
    let used = Id.Map.fold (fun id status acc -> match status.ntnvar_used with
        | [] -> assert false
        | false :: rest -> status.ntnvar_used <- rest; acc
        | true :: rest ->
          let rest = match rest with
            | [] | true :: _ -> rest
            | false :: rest -> true :: rest
          in
          status.ntnvar_used <- rest;
          Id.Set.add id acc)
        ntnvars
        Id.Set.empty
    in
    used, v
  | exception e ->
    let e = Exninfo.capture e in
    let () = Id.Map.iter (fun _ status -> status.ntnvar_used <- List.tl status.ntnvar_used) ntnvars in
    Exninfo.iraise e

let create_uniform_genconstr name =
  let tag = GenConstr.create name in
  let () = register_intern_constr tag (fun ?loc _ v -> v) in
  let () = Gensubst.register_constr_subst tag (fun _ v -> v) in
  tag
