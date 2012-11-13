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
  external equal : string -> string -> bool = "caml_string_equal" "noalloc"
  val explode : string -> string list
  val implode : string list -> string
  val strip : string -> string
  val map : (char -> char) -> string -> string
  val drop_simple_quotes : string -> string
  val string_index_from : string -> int -> string -> int
  val string_contains : where:string -> what:string -> bool
  val plural : int -> string -> string
  val ordinal : int -> string
  val split : char -> string -> string list
end

include ExtS
