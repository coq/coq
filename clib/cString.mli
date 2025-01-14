(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

  (** Equality on strings *)

  val hash : string -> int
  (** Hashing on strings. Should be compatible with generic one. *)

  val is_empty : string -> bool
  (** Test whether a string is empty. *)

  val explode : string -> string list
  (** [explode "x1...xn"] returns [["x1"; ...; "xn"]] *)

  val implode : string list -> string
  (** [implode [s1; ...; sn]] returns [s1 ^ ... ^ sn] *)

  val drop_simple_quotes : string -> string
  (** Remove the eventual first surrounding simple quotes of a string. *)

  val quote_coq_string : string -> string
  (** Quote a string according to Rocq conventions (i.e. doubling
      double quotes and surrounding by double quotes) *)

  val unquote_coq_string : string -> string option
  (** Unquote a quoted string according to Rocq conventions
      (i.e. removing surrounding double quotes and undoubling double
      quotes); returns [None] if not a quoted string *)

  val html_escape : string -> string
  (** replace HTML reserved characters with escape sequences,
      e.g. `&` -> "&#38;" *)

  val string_index_from : string -> int -> string -> int
  (** As [index_from], but takes a string instead of a char as pattern argument *)

  val string_contains : where:string -> what:string -> bool
  (** As [contains], but takes a string instead of a char as pattern argument *)

  val plural : int -> string -> string
  (** [plural n s] adds a optional 's' to the [s] when [2 <= n]. *)

  val lplural : _ list -> string -> string
  (** [lplural l s] is [plural (List.length l) s]. *)

  val conjugate_verb_to_be : int -> string
  (** [conjugate_verb_to_be] returns "is" when [n=1] and "are" otherwise *)

  val ordinal : int -> string
  (** Generate the ordinal number in English. *)

  val is_sub : string -> string -> int -> bool
  (** [is_sub p s off] tests whether [s] contains [p] at offset [off]. *)

  val is_prefix : string -> string -> bool
  (** [is_prefix p s] tests whether [p] is a prefix of [s]. *)

  val is_suffix : string -> string -> bool
  (** [is_suffix suf s] tests whether [suf] is a suffix of [s]. *)

  (** {6 Generic operations} **)

  module Set : CSet.ExtS with type elt = t
  (** Finite sets on [string] *)

  module Map : CMap.ExtS with type key = t and module Set := Set
  (** Finite maps on [string] *)

  module Pred : Predicate.S with type elt = t

  module List : CList.MonoS with type elt = t
  (** Association lists with [string] as keys *)

  val hcons : string -> string
  (** Hashconsing on [string] *)

end

include ExtS
