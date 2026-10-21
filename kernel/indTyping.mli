(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Entries
open Declarations


module NotPrimRecordReason : sig

  type t =
    | MustNotBeSquashed
    | MustHaveRelevantProj
    | MustHaveProj
    | MustNotHaveAnonProj

end

type inductive_arity = { user_arity : Constr.types; sort : Sorts.t }

(** Type checking for some inductive entry.
    Returns:
    - environment with inductives + parameters in rel context
    - abstracted universes
    - checked variance info
      (variance for section universes is at the beginning of the array)
    - record entry (checked to be OK)
    - if primitive record was requested, either: (1) if it's not ok, then why, or (2) whether it has eta
    - parameters
    - for each inductive,
      (arity * constructors) (with params)
      * (indices * splayed constructor types) (both without params)
      * top allowed elimination
 *)
val typecheck_inductive : env -> sec_univs:UVars.LevelInstance.t option
  -> mutual_inductive_entry
  -> env
  * universes
  * template_universes option
  * Names.Id.t array option option
  * (Declarations.has_eta, NotPrimRecordReason.t) result option
  * Constr.rel_context
  * ((inductive_arity * Constr.types array) *
     (Constr.rel_context * (Constr.rel_context * Constr.types) array) *
     squash_info option *
     bool (** true if the inductive relies on indices not mattering *))
    array
