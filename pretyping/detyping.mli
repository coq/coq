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
open Environ
open EConstr
open Glob_term
open Termops
open Mod_subst
open Evd
open Ltac_pretype

type _ delay =
| Now : 'a delay
| Later : [ `thunk ] delay

val subst_cases_pattern : substitution -> cases_pattern -> cases_pattern

val subst_glob_constr : env -> substitution -> glob_constr -> glob_constr

val factorize_eqns : flags:PrintingFlags.Extern.FactorizeEqns.t -> 'a cases_clauses_g -> 'a disjunctive_cases_clauses_g

(** [detype isgoal avoid ctx c] turns a closed [c], into a glob_constr
   de Bruijn indexes are turned to bound names, avoiding names in [avoid]
   [isgoal] tells if naming must avoid global-level synonyms as intro does
   [ctx] gives the names of the free variables *)

val detype : 'a delay ->
  flags:PrintingFlags.Detype.t -> ?isgoal:bool -> ?avoid:'g Namegen.Generator.input ->
  env -> evar_map -> constr -> 'a glob_constr_g

val detype_sort : universes:bool -> sorts:bool -> qualities:bool -> evar_map -> Sorts.t -> glob_sort

val detype_rel_context : 'a delay ->
  flags:PrintingFlags.Detype.t ->
  ?avoid:'g Namegen.Generator.input ->
  (names_context * env) -> evar_map -> rel_context -> 'a glob_decl_g list

val share_pattern_names :
  ('g Namegen.Generator.input -> names_context -> 'c -> 'd Pattern.constr_pattern_r -> 'a) -> int ->
  (Name.t * 'e option * binding_kind * 'b option * 'a) list ->
  'g Namegen.Generator.input -> names_context -> 'c -> 'd Pattern.constr_pattern_r ->
  'd Pattern.constr_pattern_r ->
  (Name.t * 'e option * binding_kind * 'b option * 'a) list * 'a * 'a

val detype_closed_glob : flags:PrintingFlags.Detype.t -> ?isgoal:bool ->
  ?avoid:'g Namegen.Generator.input -> env -> evar_map -> closed_glob_constr -> glob_constr

(** look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_displayed  : env -> evar_map -> constr -> Id.t -> int option
val lookup_index_as_renamed : env -> evar_map -> constr -> int -> int option
