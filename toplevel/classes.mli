(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Decl_kinds
open Term
open Context
open Evd
open Environ
open Nametab
open Mod_subst
open Constrexpr
open Typeclasses
open Implicit_quantifiers
open Libnames
open Globnames

(** Errors *)

val mismatched_params : env -> constr_expr list -> rel_context -> 'a

val mismatched_props : env -> constr_expr list -> rel_context -> 'a

(** Post-hoc class declaration. *)

val declare_class : reference -> unit

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
  Entries.proof_output -> (** body *)
  Term.types -> (** type *)
  Names.Id.t

val new_instance :
  ?abstract:bool -> (** Not abstract by default. *)
  ?global:bool -> (** Not global by default. *)
  local_binder list ->
  typeclass_constraint ->
  constr_expr option ->
  ?generalize:bool ->
  ?tac:Proof_type.tactic  ->
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
val context : local_binder list -> bool

(** Forward ref for refine *)

val refine_ref : (open_constr -> Proof_type.tactic) ref
