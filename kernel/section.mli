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
open Univ
open UVars
open Cooking

(** Kernel implementation of sections. *)

type 'a t
(** Type of sections with additional data ['a] *)

val depth : 'a t -> int
(** Number of nested sections. *)

val map_custom : ('a -> 'a) -> 'a t -> 'a t
(** Modify the custom data *)

(** {6 Manipulating sections} *)

type section_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

val open_section : custom:'a -> 'a t option -> 'a t
(** Open a new section with the provided universe polymorphic status. Sections
    can be nested, with the proviso that polymorphic sections cannot appear
    inside a monomorphic one. A custom data can be attached to this section,
    that will be returned by {!close_section}. *)

val close_section : 'a t -> 'a t option * section_entry list * ContextSet.t * 'a
(** Close the current section and returns the entries defined inside, the set
    of global monomorphic constraints added in this section, and the custom data
    provided at the opening of the section. *)

(** {6 Extending sections} *)

val push_local : Constr.named_declaration -> 'a t -> 'a t
(** Extend the current section with a local definition (cf. push_named). *)

val push_local_universe_context : UContext.t -> 'a t -> 'a t
(** Extend the current section with a local universe context. Assumes that the
    last opened section is polymorphic. *)

val push_constraints : ContextSet.t -> 'a t -> 'a t
(** Extend the current section with a global universe context.
    Assumes that the last opened section is monomorphic. *)

val push_global : Environ.env -> poly:bool -> section_entry -> 'a t -> 'a t
(** Push a global entry in this section. *)

(** {6 Retrieving section data} *)

val all_poly_univs : 'a t -> Instance.t
(** Returns all polymorphic universes, including those from previous
   sections. Earlier sections are earlier in the array.

    NB: even if the array is empty there may be polymorphic
   constraints about monomorphic universes, which prevent declaring
   monomorphic globals. *)

val segment_of_constant : Constant.t -> 'a t -> cooking_info
(** Section segment at the time of the constant declaration *)

val segment_of_inductive : MutInd.t -> 'a t -> cooking_info
(** Section segment at the time of the inductive declaration *)

val is_in_section : Environ.env -> GlobRef.t -> 'a t -> bool
