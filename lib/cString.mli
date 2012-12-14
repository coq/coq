(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** FIXME: From OCaml 3.12 onwards, that would only be a [module type of] *)

(** Module type [S] is the one from OCaml Stdlib. *)
module type S =
sig
  external length : string -> int = "%string_length"
  external get : string -> int -> char = "%string_safe_get"
  external set : string -> int -> char -> unit = "%string_safe_set"
  external create : int -> string = "caml_create_string"
  val make : int -> char -> string
  val copy : string -> string
  val sub : string -> int -> int -> string
  val fill : string -> int -> int -> char -> unit
  val blit : string -> int -> string -> int -> int -> unit
  val concat : string -> string list -> string
  val iter : (char -> unit) -> string -> unit
  val escaped : string -> string
  val index : string -> char -> int
  val rindex : string -> char -> int
  val index_from : string -> int -> char -> int
  val rindex_from : string -> int -> char -> int
  val contains : string -> char -> bool
  val contains_from : string -> int -> char -> bool
  val rcontains_from : string -> int -> char -> bool
  val uppercase : string -> string
  val lowercase : string -> string
  val capitalize : string -> string
  val uncapitalize : string -> string
  type t = string
  val compare: t -> t -> int
  external unsafe_get : string -> int -> char = "%string_unsafe_get"
  external unsafe_set : string -> int -> char -> unit = "%string_unsafe_set"
  external unsafe_blit :
    string -> int -> string -> int -> int -> unit = "caml_blit_string" "noalloc"
  external unsafe_fill :
    string -> int -> int -> char -> unit = "caml_fill_string" "noalloc"
end

module type ExtS =
sig
  include S
  (** We include the standard library *)

  external equal : string -> string -> bool = "caml_string_equal" "noalloc"
  (** Equality on strings *)

  val is_empty : string -> bool
  (** Test whether a string is empty. *)

  val explode : string -> string list
  (** [explode "x1...xn"] returns [["x1"; ...; "xn"]] *)

  val implode : string list -> string
  (** [implode [s1; ...; sn]] returns [s1 ^ ... ^ sn] *)

  val strip : string -> string
  (** Remove the surrounding blank characters from a string *)

  val map : (char -> char) -> string -> string
  (** Apply a function on a string character-wise. *)

  val drop_simple_quotes : string -> string
  (** Remove the eventual first surrounding simple quotes of a string. *)

  val string_index_from : string -> int -> string -> int
  (** As [index_from], but takes a string instead of a char as pattern argument *)

  val string_contains : where:string -> what:string -> bool
  (** As [contains], but takes a string instead of a char as pattern argument *)

  val plural : int -> string -> string
  (** [plural n s] adds a optional 's' to the [s] when [2 <= n]. *)

  val ordinal : int -> string
  (** Generate the ordinal number in English. *)

  val split : char -> string -> string list
  (** [split c s] splits [s] into sequences separated by [c], excluded. *)

  val is_sub : string -> string -> int -> bool
  (** [is_sub p s off] tests whether [s] contains [p] at offset [off]. *)

  (** {6 Generic operations} **)

  module Set : Set.S with type elt = t
  (** Finite sets on [string] *)

  module Map : Map.S with type key = t
  (** Finite maps on [string] *)

  val hcons : string -> string
  (** Hashconsing on [string] *)

end

include ExtS
