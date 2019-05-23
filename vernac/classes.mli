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

val declare_instance : ?warn:bool -> env -> Evd.evar_map ->
                       hint_info option -> bool -> GlobRef.t -> unit
(** Declares the given global reference as an instance of its type.
    Does nothing — or emit a “not-a-class” warning if the [warn] argument is set —
    when said type is not a registered type class. *)

val existing_instance : bool -> qualid -> Hints.hint_info_expr option -> unit
(** globality, reference, optional priority and pattern information *)

val new_instance :
  pstate:Proof_global.t option
  -> ?global:bool (** Not global by default. *)
  -> program_mode:bool
  -> Decl_kinds.polymorphic
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> (bool * constr_expr) option
  -> ?generalize:bool
  -> ?tac:unit Proofview.tactic
  -> ?hook:(GlobRef.t -> unit)
  -> Hints.hint_info_expr
  -> Id.t * Proof_global.t option (* May open a proof *)

val declare_new_instance
  : ?global:bool (** Not global by default. *)
  -> program_mode:bool
  -> Decl_kinds.polymorphic
  -> ident_decl
  -> local_binder_expr list
  -> constr_expr
  -> Hints.hint_info_expr
  -> unit

(** {6 Low level interface used by Add Morphism, do not use } *)
val mk_instance : typeclass -> hint_info -> bool -> GlobRef.t -> instance
val add_instance : instance -> unit

val add_class : env -> Evd.evar_map -> typeclass -> unit

(** Setting opacity *)

val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> Id.t
