(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util
open Typeclasses
open Implicit_quantifiers
open Libnames

(** Errors *)

val mismatched_params : env -> constr_expr list -> rel_context -> 'a

val mismatched_props : env -> constr_expr list -> rel_context -> 'a

(** Post-hoc class declaration. *)

val declare_class : reference -> unit

(** Instance declaration *)

val declare_instance : bool -> reference -> unit

val declare_instance_constant :
  typeclass ->
  int option -> (** priority *)
  bool -> (** globality *)
  Impargs.manual_explicitation list -> (** implicits *)
  ?hook:(Libnames.global_reference -> unit) ->
  polymorphic ->
  identifier -> (** name *)
  Term.constr -> (** body *)
  Term.types -> (** type *)
  Names.identifier

val new_instance :
  ?abstract:bool -> (** Not abstract by default. *)
  ?global:bool -> (** Not global by default. *)
  polymorphic ->
  local_binder list ->
  typeclass_constraint ->
  constr_expr option ->
  ?generalize:bool ->
  ?tac:Proof_type.tactic  ->
  ?hook:(Libnames.global_reference -> unit) ->
  int option ->
  identifier

(** Setting opacity *)

val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> identifier

(** Context command *)

val context : local_binder list -> unit

(** Forward ref for refine *)

val refine_ref : (open_constr -> Proof_type.tactic) ref

