(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open Constrexpr
open Typeclasses
open Libnames

(** Errors *)

val mismatched_params : env -> constr_expr list -> Constr.rel_context -> 'a

val mismatched_props : env -> constr_expr list -> Constr.rel_context -> 'a

(** Instance declaration *)

val existing_instance : bool -> qualid -> Hints.hint_info_expr option -> unit
(** globality, reference, optional priority and pattern information *)

val declare_instance_constant :
  typeclass ->
  Hints.hint_info_expr -> (** priority *)
  bool -> (** globality *)
  Impargs.manual_explicitation list -> (** implicits *)
  ?hook:(GlobRef.t -> unit) ->
  Id.t -> (** name *)
  UState.universe_decl ->
  bool -> (* polymorphic *)
  Evd.evar_map -> (* Universes *)
  Constr.t -> (** body *)
  Constr.types -> (** type *)
  Names.Id.t

val new_instance :
  ?abstract:bool -> (** Not abstract by default. *)
  ?global:bool -> (** Not global by default. *)
  ?refine:bool -> (** Allow refinement *)
  program_mode:bool ->
  Decl_kinds.polymorphic ->
  local_binder_expr list ->
  Vernacexpr.typeclass_constraint ->
  (bool * constr_expr) option ->
  ?generalize:bool ->
  ?tac:unit Proofview.tactic  ->
  ?hook:(GlobRef.t -> unit) ->
  Hints.hint_info_expr ->
  Id.t

(** Setting opacity *)

val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> Id.t

(** Context command *)

(** returns [false] if, for lack of section, it declares an assumption
    (unless in a module type). *)
val context : Decl_kinds.polymorphic -> local_binder_expr list -> bool
