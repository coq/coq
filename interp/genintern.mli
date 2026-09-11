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

module Store : Store.S

type ntnvar_status = {
  (* list so that we can separate using a variable in different subterms *)
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

val empty_glob_sign : strict:bool -> Environ.env -> UnivNames.universe_binders -> glob_sign

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * Constrexpr.constr_expr option
type glob_constr_pattern_and_expr = Id.Set.t * glob_constr_and_expr * Pattern.uninstantiated_pattern

(** {5 Internalization functions} *)

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
(** The type of functions used for internalizing generic arguments. *)

type ('raw, 'glb) constr_intern_fun = ?loc:Loc.t -> glob_sign -> 'raw -> 'glb

type constr_intern_info = { passthrough_impls : bool }

val intern : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) intern_fun

val generic_intern : (raw_generic_argument, glob_generic_argument) intern_fun

val generic_intern_constr : (GenConstr.raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun

(** {5 Internalization in tactic patterns} *)

val generic_intern_pat : (GenConstr.raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun

(** {5 Notation functions} *)

(* [ntnvar_status Id.Map.t]: surrounding notation variables
   [id -> glob_constr option]: substitution for previous notation variables,
   may raise an exception if it fails, None for recursive part variables *)
type 'glb ntn_subst_fun = ntnvar_status Id.Map.t -> (Id.t -> Glob_term.glob_constr option) -> 'glb -> 'glb

val substitute_notation : (_, 'glb) GenConstr.tag -> 'glb ntn_subst_fun

val generic_substitute_notation : GenConstr.glb ntn_subst_fun

(** Registering functions *)

val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
  ('raw, 'glb) intern_fun -> unit

val register_intern_constr : ('raw, 'glb) GenConstr.tag ->
  ('raw, 'glb) constr_intern_fun -> unit

val register_intern_pat : ('raw, 'glb) GenConstr.tag ->
  ('raw, 'glb) constr_intern_fun -> unit

val register_intern_constr_gen : ('raw, Util.Empty.t) GenConstr.tag ->
  ('raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun -> unit

val register_intern_pat_gen : ('raw, Util.Empty.t) GenConstr.tag ->
  ('raw, Glob_term.glob_constr * constr_intern_info) constr_intern_fun -> unit

val register_ntn_subst0 : (_, 'glb) GenConstr.tag -> 'glb ntn_subst_fun -> unit

(** Used to compute the set of used notation variables during internalization.*)
val with_used_ntnvars : ntnvar_status Id.Map.t -> (unit -> 'a) -> Id.Set.t * 'a

(** Registers trivial intern and subst functions. Other registers
    should be done by the caller. *)
val create_uniform_genconstr : string -> ('a, 'a) GenConstr.tag
