(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ

(** Kernel implementation of sections. *)

type 'a t
(** Type of sections with additional data ['a] *)

val empty : 'a t

val is_empty : 'a t -> bool
(** Checks whether there is no opened section *)

(** {6 Manipulating sections} *)

type section_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

val open_section : custom:'a -> 'a t -> 'a t
(** Open a new section with the provided universe polymorphic status. Sections
    can be nested, with the proviso that polymorphic sections cannot appear
    inside a monomorphic one. A custom data can be attached to this section,
    that will be returned by {!close_section}. *)

val close_section : 'a t -> 'a t * section_entry list * ContextSet.t * 'a
(** Close the current section and returns the entries defined inside, the set
    of global monomorphic constraints added in this section, and the custom data
    provided at the opening of the section. *)

(** {6 Extending sections} *)

val push_local : 'a t -> 'a t
(** Extend the current section with a local definition (cf. push_named). *)

val push_context : Name.t array * UContext.t -> 'a t -> 'a t
(** Extend the current section with a local universe context. Assumes that the
    last opened section is polymorphic. *)

val push_constraints : ContextSet.t -> 'a t -> 'a t
(** Extend the current section with a global universe context.
    Assumes that the last opened section is monomorphic. *)

val push_constant : poly:bool -> Constant.t -> 'a t -> 'a t
(** Make the constant as having been defined in this section. *)

val push_inductive : poly:bool -> MutInd.t -> 'a t -> 'a t
(** Make the inductive block as having been defined in this section. *)

(** {6 Retrieving section data} *)

type abstr_info = private {
  abstr_ctx : Constr.named_context;
  (** Section variables of this prefix *)
  abstr_subst : Univ.Instance.t;
  (** Actual names of the abstracted variables *)
  abstr_uctx : Univ.AUContext.t;
  (** Universe quantification, same length as the substitution *)
}
(** Data needed to abstract over the section variable and universe hypotheses *)


val empty_segment : abstr_info
(** Nothing to abstract *)

val segment_of_constant : Environ.env -> Constant.t -> 'a t -> abstr_info
(** Section segment at the time of the constant declaration *)

val segment_of_inductive : Environ.env -> MutInd.t -> 'a t -> abstr_info
(** Section segment at the time of the inductive declaration *)

val replacement_context : Environ.env -> 'a t -> Opaqueproof.work_list
(** Section segments of all declarations from this section. *)

val is_in_section : Environ.env -> GlobRef.t -> 'a t -> bool

val is_polymorphic_univ : Level.t -> 'a t -> bool
