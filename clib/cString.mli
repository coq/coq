(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Module type [S] is the one from OCaml Stdlib. *)
module type S = module type of String

module type ExtS =
sig
  include S
  (** We include the standard library *)

  [@@@ocaml.warning "-3"]     (* [@@noalloc] since 4.03.0 GPR#240 *)
  external equal : string -> string -> bool = "caml_string_equal" "noalloc"
  [@@@ocaml.warning "+3"]

  (** Equality on strings *)

  val hash : string -> int
  (** Hashing on strings. Should be compatible with generic one. *)

  val is_empty : string -> bool
  (** Test whether a string is empty. *)

  val explode : string -> string list
  (** [explode "x1...xn"] returns [["x1"; ...; "xn"]] *)

  val implode : string list -> string
  (** [implode [s1; ...; sn]] returns [s1 ^ ... ^ sn] *)

  val strip : string -> string
  (** Remove the surrounding blank characters from a string *)

  val drop_simple_quotes : string -> string
  (** Remove the eventual first surrounding simple quotes of a string. *)

  val string_index_from : string -> int -> string -> int
  (** As [index_from], but takes a string instead of a char as pattern argument *)

  val string_contains : where:string -> what:string -> bool
  (** As [contains], but takes a string instead of a char as pattern argument *)

  val plural : int -> string -> string
  (** [plural n s] adds a optional 's' to the [s] when [2 <= n]. *)

  val conjugate_verb_to_be : int -> string
  (** [conjugate_verb_to_be] returns "is" when [n=1] and "are" otherwise *)

  val ordinal : int -> string
  (** Generate the ordinal number in English. *)

  val split : char -> string -> string list
  (** [split c s] splits [s] into sequences separated by [c], excluded. *)

  val is_sub : string -> string -> int -> bool
  (** [is_sub p s off] tests whether [s] contains [p] at offset [off]. *)

  (** {6 Generic operations} **)

  module Set : Set.S with type elt = t
  (** Finite sets on [string] *)

  module Map : CMap.ExtS with type key = t and module Set := Set
  (** Finite maps on [string] *)

  module List : CList.MonoS with type elt = t
  (** Association lists with [string] as keys *)

  val hcons : string -> string
  (** Hashconsing on [string] *)

end

include ExtS
