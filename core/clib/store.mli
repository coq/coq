(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*** This module implements an "untyped store", in this particular case we
        see it as an extensible record whose fields are left unspecified. ***)

module type S =
sig
  type t
  (** Type of stores *)

  type 'a field
  (** Type of field of such stores *)

  val field : unit -> 'a field
  (** Create a new field *)

  val empty : t
  (** Empty store *)

  val set : t -> 'a field -> 'a -> t
  (** Set a field *)

  val get : t -> 'a field -> 'a option
  (** Get the value of a field, if any *)

  val remove : t -> 'a field -> t
  (** Unset the value of the field *)

  val merge : t -> t -> t
  (** [merge s1 s2] adds all the fields of [s1] into [s2]. *)
end

module Make() : S
(** Create a new store type. *)
