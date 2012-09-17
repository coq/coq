(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module contains numerous utility functions on strings, lists,
   arrays, etc. *)

(** Mapping under pairs *)

val on_fst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
val on_snd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
val map_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b

(** Going down pairs *)

val down_fst : ('a -> 'b) -> 'a * 'c -> 'b
val down_snd : ('a -> 'b) -> 'c * 'a -> 'b

(** Mapping under triple *)

val on_pi1 : ('a -> 'b) -> 'a * 'c * 'd -> 'b * 'c * 'd
val on_pi2 : ('a -> 'b) -> 'c * 'a * 'd -> 'c * 'b * 'd
val on_pi3 : ('a -> 'b) -> 'c * 'd * 'a -> 'c * 'd * 'b

(** {6 Projections from triplets } *)

val pi1 : 'a * 'b * 'c -> 'a
val pi2 : 'a * 'b * 'c -> 'b
val pi3 : 'a * 'b * 'c -> 'c

(** {6 Chars. } *)

val is_letter : char -> bool
val is_digit : char -> bool
val is_ident_tail : char -> bool
val is_blank : char -> bool
val next_utf8 : string -> int -> int * int

(** {6 Strings. } *)

val explode : string -> string list
val implode : string list -> string
val strip : string -> string
val string_map : (char -> char) -> string -> string
val drop_simple_quotes : string -> string
val string_index_from : string -> int -> string -> int
val string_string_contains : where:string -> what:string -> bool
val plural : int -> string -> string
val ordinal : int -> string
val split_string_at : char -> string -> string list

(** Substitute %s in the first chain by the second chain *)
val subst_command_placeholder : string -> string -> string
val parse_loadpath : string -> string list

module Stringset : Set.S with type elt = string
module Stringmap : Map.S with type key = string

type utf8_status = UnicodeLetter | UnicodeIdentPart | UnicodeSymbol

exception UnsupportedUtf8

val ident_refutation : string -> (bool * string) option
val classify_unicode : int -> utf8_status
val lowercase_first_char_utf8 : string -> string
val ascii_of_ident : string -> string

(** {6 Lists. } *)

module List : CList.ExtS

val (@) : 'a list -> 'a list -> 'a list

(** {6 Arrays. } *)

module Array : CArray.ExtS

(** {6 Streams. } *)

val stream_nth : int -> 'a Stream.t -> 'a
val stream_njunk : int -> 'a Stream.t -> unit

(** {6 Matrices. } *)

val matrix_transpose : 'a list list -> 'a list list

(** {6 Functions. } *)

val identity : 'a -> 'a
val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val const : 'a -> 'b -> 'a
val iterate : ('a -> 'a) -> int -> 'a -> 'a
val repeat : int -> ('a -> unit) -> 'a -> unit
val iterate_for : int -> int -> (int -> 'a -> 'a) -> 'a -> 'a
val app_opt : ('a -> 'a) option -> 'a -> 'a

(** {6 Delayed computations. } *)

type 'a delayed = unit -> 'a

val delayed_force : 'a delayed -> 'a

(** {6 Misc. } *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset : Set.S with type elt = int

module Intmap : Map.S with type key = int

val intmap_in_dom : int -> 'a Intmap.t -> bool
val intmap_to_list : 'a Intmap.t -> (int * 'a) list
val intmap_inv : 'a Intmap.t -> 'a -> int list

val interval : int -> int -> int list

(** {6 Memoization. } *)

(** General comments on memoization:
   - cache is created whenever the function is supplied (because of
      ML's polymorphic value restriction).
   - cache is never flushed (unless the memoized fun is GC'd)
 
   One cell memory: memorizes only the last call *)
val memo1_1 : ('a -> 'b) -> ('a -> 'b)
val memo1_2 : ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)

(** with custom equality (used to deal with various arities) *)
val memo1_eq : ('a -> 'a -> bool) -> ('a -> 'b) -> ('a -> 'b)

(** Memorizes the last [n] distinct calls. Efficient only for small [n]. *)
val memon_eq : ('a -> 'a -> bool) -> int -> ('a -> 'b) -> ('a -> 'b)

(** {6 Size of an ocaml value (in words, bytes and kilobytes). } *)

val size_w : 'a -> int
val size_b : 'a -> int
val size_kb : 'a -> int

(** {6 Total size of the allocated ocaml heap. } *)

val heap_size : unit -> int
val heap_size_kb : unit -> int

(** {6 ... } *)
(** Coq interruption: set the following boolean reference to interrupt Coq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val interrupt : bool ref
val check_for_interrupt : unit -> unit
