(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

type t
(** Values of this type represent (Coq) identifiers. *)

val equal : t -> t -> bool
(** Equality over identifiers. *)

val compare : t -> t -> int
(** Comparison over identifiers. *)

val hash : t -> int
(** Hash over identifiers. *)

val is_valid : string -> bool
(** Check that a string may be converted to an identifier. *)

val is_valid_ident_part : string -> bool
(** Check that a string is a valid part of an identifier *)

val of_bytes : bytes -> t
val of_string : string -> t
(** Converts a string into an identifier.
    @raise UserError if the string is invalid as an identifier. *)

val of_string_soft : string -> t
(** Same as {!of_string} except that any string made of supported UTF-8 characters is accepted.
    @raise UserError if the string is invalid as an UTF-8 string. *)

val to_string : t -> string
(** Converts a identifier into an string. *)

val print : t -> Pp.t
(** Pretty-printer. *)

module Set : Set.S with type elt = t
(** Finite sets of identifiers. *)

module Map : Map.ExtS with type key = t and module Set := Set
(** Finite maps of identifiers. *)

module Pred : Predicate.S with type elt = t
(** Predicates over identifiers. *)

module List : List.MonoS with type elt = t
(** Operations over lists of identifiers. *)

val hcons : t -> t
(** Hashconsing of identifiers. *)
