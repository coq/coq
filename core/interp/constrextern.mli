(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Termops
open EConstr
open Environ
open Libnames
open Glob_term
open Pattern
open Constrexpr
open Notation_term
open Notation
open Ltac_pretype

(** Translation of pattern, cases pattern, glob_constr and term into syntax
   trees for printing *)

type extern_env = Id.Set.t * UnivNames.universe_binders
val extern_env : env -> Evd.evar_map -> extern_env

val extern_cases_pattern : Id.Set.t -> 'a cases_pattern_g -> cases_pattern_expr
val extern_glob_constr : extern_env -> 'a glob_constr_g -> constr_expr
val extern_glob_type : ?impargs:Glob_term.binding_kind list -> extern_env -> 'a glob_constr_g -> constr_expr
val extern_constr_pattern : names_context -> Evd.evar_map ->
  constr_pattern -> constr_expr
val extern_closed_glob : ?lax:bool -> ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name ->
  env -> Evd.evar_map -> closed_glob_constr -> constr_expr

(** If [b=true] in [extern_constr b env c] then the variables in the first
   level of quantification clashing with the variables in [env] are renamed.
    ~lax is for debug printing, when the constr might not be well typed in
    env, sigma
*)

val extern_constr : ?lax:bool -> ?inctx:bool -> ?scope:scope_name ->
  env -> Evd.evar_map -> constr -> constr_expr
val extern_constr_in_scope : ?lax:bool -> ?inctx:bool -> scope_name ->
  env -> Evd.evar_map -> constr -> constr_expr
val extern_reference : ?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid
val extern_type : ?lax:bool -> ?goal_concl_style:bool -> env -> Evd.evar_map -> ?impargs:Glob_term.binding_kind list -> types -> constr_expr
val extern_sort : Evd.evar_map -> Sorts.t -> sort_expr
val extern_rel_context : constr option -> env -> Evd.evar_map ->
  rel_context -> local_binder_expr list

(** Printing options *)
val print_implicits : bool ref
val print_implicits_defensive : bool ref
val print_arguments : bool ref
val print_evar_arguments : bool ref
val print_coercions : bool ref
val print_parentheses : bool ref
val print_universes : bool ref
val print_no_symbol : bool ref
val print_projections : bool ref
val print_raw_literal : bool ref

(** Customization of the global_reference printer *)
val set_extern_reference :
  (?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid) -> unit
val get_extern_reference :
  unit -> (?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid)

(** WARNING: The following functions are evil due to
    side-effects. Think of the following case as used in the printer:

    without_specific_symbols [SynDefRule kn] (pr_glob_constr_env env) c

    vs

    without_specific_symbols [SynDefRule kn] pr_glob_constr_env env c

    which one is wrong? We should turn this kind of state into an
    explicit argument.
*)

(** This forces printing universe names of Type\{.\} *)
val with_universes : ('a -> 'b) -> 'a -> 'b

(** This suppresses printing of primitive tokens and notations *)
val without_symbols : ('a -> 'b) -> 'a -> 'b

(** This suppresses printing of specific notations only *)
val without_specific_symbols : interp_rule list -> ('a -> 'b) -> 'a -> 'b

(** This prints metas as anonymous holes *)
val with_meta_as_hole : ('a -> 'b) -> 'a -> 'b

(** Fine-grained activation and deactivation of notation printing.
 *)
val toggle_scope_printing :
  scope:Notation_term.scope_name -> activate:bool -> unit

val toggle_notation_printing
  : ?scope:Notation_term.scope_name
  -> notation:Constrexpr.notation
  -> activate:bool
  -> unit
  -> unit

(** Probably shouldn't be used *)
val empty_extern_env : extern_env
