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
open Termops
open EConstr
open Environ
open Libnames
open Glob_term
open Pattern
open Constrexpr
open Notation_term
open Ltac_pretype

(** Translation of pattern, cases pattern, glob_constr and term into syntax
   trees for printing *)

type extern_env = {
  vars : Id.Set.t;
  uvars : UnivNames.universe_binders;
  flags : PrintingFlags.Extern.t;
}
val extern_env : flags:PrintingFlags.Extern.t -> env -> Evd.evar_map -> extern_env

val extern_cases_pattern : flags:PrintingFlags.Extern.t -> Id.Set.t -> 'a cases_pattern_g -> cases_pattern_expr
val extern_glob_constr : extern_env -> 'a glob_constr_g -> constr_expr
val extern_glob_type : ?impargs:Glob_term.binding_kind list -> extern_env -> 'a glob_constr_g -> constr_expr
val extern_constr_pattern : flags:PrintingFlags.Extern.t -> names_context -> Evd.evar_map ->
  constr_pattern -> constr_expr
val extern_uninstantiated_pattern : flags:PrintingFlags.Extern.t -> names_context -> Evd.evar_map ->
  uninstantiated_pattern -> constr_expr
val extern_closed_glob : ?goal_concl_style:bool -> ?inctx:bool -> ?scope:scope_name ->
  flags:PrintingFlags.t -> env -> Evd.evar_map -> closed_glob_constr -> constr_expr

(** If [b=true] in [extern_constr b env c] then the variables in the first
   level of quantification clashing with the variables in [env] are renamed.
    ~lax is for debug printing, when the constr might not be well typed in
    env, sigma
*)

val extern_constr : ?inctx:bool -> ?scope:scope_name ->
  flags:PrintingFlags.t -> env -> Evd.evar_map -> constr -> constr_expr
val extern_constr_in_scope : ?inctx:bool -> scope_name ->
  flags:PrintingFlags.t -> env -> Evd.evar_map -> constr -> constr_expr
val extern_reference : ?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid
val extern_type : ?goal_concl_style:bool ->
  flags:PrintingFlags.t -> env -> Evd.evar_map ->
  ?impargs:Glob_term.binding_kind list -> types -> constr_expr
val extern_sort : universes:bool -> sorts:bool -> qualities:bool -> Evd.evar_map -> Sorts.t -> sort_expr
val extern_rel_context : flags:PrintingFlags.t -> env -> Evd.evar_map ->
  rel_context -> local_binder_expr list

(** Customization of the global_reference printer *)
val set_extern_reference :
  (?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid) -> unit
val get_extern_reference :
  unit -> (?loc:Loc.t -> Id.Set.t -> GlobRef.t -> qualid)

(** Probably shouldn't be used *)
val empty_extern_env : flags:PrintingFlags.Extern.t -> extern_env

val set_max_depth : int option -> unit
