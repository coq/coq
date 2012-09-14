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

(** {6 Arrays. } *)

val array_compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
val array_equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
val array_exists : ('a -> bool) -> 'a array -> bool
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
val array_for_all3 : ('a -> 'b -> 'c -> bool) ->
  'a array -> 'b array -> 'c array -> bool
val array_for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
  'a array -> 'b array -> 'c array -> 'd array -> bool
val array_for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool
val array_find_i : (int -> 'a -> bool) -> 'a array -> int option
val array_hd : 'a array -> 'a
val array_tl : 'a array -> 'a array
val array_last : 'a array -> 'a
val array_cons : 'a -> 'a array -> 'a array
val array_rev : 'a array -> unit
val array_fold_right_i :
  (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
val array_fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
val array_fold_right2 :
  ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
val array_fold_left2 :
  ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
val array_fold_left3 :
  ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'a
val array_fold_left2_i :
  (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
val array_fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_map_to_list : ('a -> 'b) -> 'a array -> 'b list
val array_chop : int -> 'a array -> 'a array * 'a array
val array_smartmap : ('a -> 'a) -> 'a array -> 'a array
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map3 :
  ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
val array_map_left : ('a -> 'b) -> 'a array -> 'b array
val array_map_left_pair : ('a -> 'b) -> 'a array -> ('c -> 'd) -> 'c array ->
  'b array * 'd array
val array_iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
val array_fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
val array_fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
val array_fold_map2' :
  ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
val array_distinct : 'a array -> bool
val array_union_map : ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
val array_rev_to_list : 'a array -> 'a list
val array_filter_along : ('a -> bool) -> 'a list -> 'b array -> 'b array
val array_filter_with : bool list -> 'a array -> 'a array

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


(** In [map_succeed f l] an element [a] is removed if [f a] raises 
   [Failure _] otherwise behaves as [List.map f l] *)

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

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
