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
open Environ
open Constrexpr
open Typeclasses
open Libnames

(** Instance declaration *)

val declare_instance : ?warn:bool -> env -> Evd.evar_map ->
                       hint_info option -> Goptions.option_locality -> GlobRef.t -> unit
(** Declares the given global reference as an instance of its type.
    Does nothing — or emit a “not-a-class” warning if the [warn] argument is set —
    when said type is not a registered type class. *)

val existing_instance : Goptions.option_locality -> qualid -> Vernacexpr.hint_info_expr option -> unit
(** globality, reference, optional priority and pattern information *)

val new_instance_interactive
  :  ?locality:Goptions.option_locality (** Not global by default. *)
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> ?generalize:bool
  -> ?tac:unit Proofview.tactic
  -> ?hook:(GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> (bool * constr_expr) option
  -> Id.t * Declare.Proof.t

val new_instance
  :  ?locality:Goptions.option_locality (** Not global by default. *)
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> (bool * constr_expr)
  -> ?generalize:bool
  -> ?hook:(GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> Id.t

val new_instance_program
  : ?locality:Goptions.option_locality (** Not global by default. *)
  -> pm:Declare.OblState.t
  -> poly:bool
  -> name_decl
  -> local_binder_expr list
  -> constr_expr
  -> (bool * constr_expr) option
  -> ?generalize:bool
  -> ?hook:(GlobRef.t -> unit)
  -> Vernacexpr.hint_info_expr
  -> Declare.OblState.t * Id.t

val declare_new_instance
  : ?locality:Goptions.option_locality (** Not global by default. *)
  -> program_mode:bool
  -> poly:bool
  -> ident_decl
  -> local_binder_expr list
  -> constr_expr
  -> Vernacexpr.hint_info_expr
  -> unit

val add_class : env -> Evd.evar_map -> typeclass -> unit

(** Setting opacity *)

val set_typeclass_transparency : Tacred.evaluable_global_reference -> bool -> bool -> unit

(** For generation on names based on classes only *)

val id_of_class : typeclass -> Id.t

val refine_att : bool Attributes.attribute

(** {6 Low level interface used by Add Morphism, do not use } *)
module Internal :
sig
val add_instance : typeclass -> hint_info -> bool -> GlobRef.t -> unit
end
