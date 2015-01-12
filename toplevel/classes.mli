(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Context
open Evd
open Environ
open Constrexpr
open Typeclasses
open Libnames

(** Errors *)

val mismatched_params : env -> constr_expr list -> rel_context -> 'a

val mismatched_props : env -> constr_expr list -> rel_context -> 'a

(** Instance declaration *)

val existing_instance : bool -> reference -> int option -> unit
(** globality, reference, priority *)

val declare_instance_constant :
  typeclass ->
  int option -> (** priority *)
  bool -> (** globality *)
  Impargs.manual_explicitation list -> (** implicits *)
  ?hook:(Globnames.global_reference -> unit) ->
  Id.t -> (** name *)
  bool -> (* polymorphic *)
  Univ.universe_context -> (* Universes *)
  Constr.t -> (** body *)
  Term.types -> (** type *)
  Names.Id.t

val new_instance :
  ?abstract:bool -> (** Not abstract by default. *)
  ?global:bool -> (** Not global by default. *)
  Decl_kinds.polymorphic ->
  local_binder list ->
  typeclass_constraint ->
  (bool * constr_expr) option ->
  ?generalize:bool ->
  ?tac:unit Proofview.tactic  ->
  ?hook:(Globnames.global_reference -> unit) ->
  int option ->
  Id.t

(** Setting opacity *)

val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> Id.t

(** Context command *)

(** returns [false] if, for lack of section, it declares an assumption
    (unless in a module type). *)
val context : Decl_kinds.polymorphic -> local_binder list -> bool
