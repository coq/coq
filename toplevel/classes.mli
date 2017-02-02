(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Environ
open Constrexpr
open Typeclasses
open Libnames

(** Errors *)

val mismatched_params : env -> constr_expr list -> Context.Rel.t -> 'a

val mismatched_props : env -> constr_expr list -> Context.Rel.t -> 'a

(** Instance declaration *)

val existing_instance : bool -> reference -> Vernacexpr.hint_info_expr option -> unit
(** globality, reference, optional priority and pattern information *)

val declare_instance_constant :
  typeclass ->
  Vernacexpr.hint_info_expr -> (** priority *)
  bool -> (** globality *)
  Impargs.manual_explicitation list -> (** implicits *)
  ?hook:(Globnames.global_reference -> unit) ->
  Id.t -> (** name *)
  Id.t Loc.located list option ->
  bool -> (* polymorphic *)
  Evd.evar_map -> (* Universes *)
  Constr.t -> (** body *)
  Term.types -> (** type *)
  Names.Id.t

val new_instance :
  ?abstract:bool -> (** Not abstract by default. *)
  ?global:bool -> (** Not global by default. *)
  ?refine:bool -> (** Allow refinement *)
  Decl_kinds.polymorphic ->
  local_binder_expr list ->
  typeclass_constraint ->
  (bool * constr_expr) option ->
  ?generalize:bool ->
  ?tac:unit Proofview.tactic  ->
  ?hook:(Globnames.global_reference -> unit) ->
  Vernacexpr.hint_info_expr ->
  Id.t

(** Setting opacity *)

val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> Id.t

(** Context command *)

(** returns [false] if, for lack of section, it declares an assumption
    (unless in a module type). *)
val context : Decl_kinds.polymorphic -> local_binder_expr list -> bool
