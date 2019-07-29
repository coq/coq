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

type t
(** Type of sections *)

val empty : t

val is_empty : t -> bool
(** Checks whether there is no opened section *)

val is_polymorphic : t -> bool
(** Checks whether last opened section is polymorphic *)

(** {6 Manipulating sections} *)

val open_section : poly:bool -> t -> t
(** Open a new section with the provided universe polymorphic status. Sections
    can be nested, with the proviso that polymorphic sections cannot appear
    inside a monomorphic one. *)

val close_section : t -> t

(** {6 Extending sections} *)

val push_local : t -> t
(** Extend the current section with a local definition (cf. push_named). *)

val push_context : Name.t array * UContext.t -> t -> t
(** Extend the current section with a local universe context. Assumes that the
    last opened section is polymorphic. *)

val push_constant : poly:bool -> Constant.t -> t -> t
(** Make the constant as having been defined in this section. *)

val push_inductive : poly:bool -> MutInd.t -> t -> t
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

val segment_of_constant : Environ.env -> Constant.t -> t -> abstr_info
(** Section segment at the time of the constant declaration *)

val segment_of_inductive : Environ.env -> MutInd.t -> t -> abstr_info
(** Section segment at the time of the inductive declaration *)

val replacement_context : Environ.env -> t -> Opaqueproof.work_list
(** Section segments of all declarations from this section. *)

val is_in_section : Environ.env -> GlobRef.t -> t -> bool

val is_polymorphic_univ : Level.t -> t -> bool
