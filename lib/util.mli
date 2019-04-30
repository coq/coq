(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module contains numerous utility functions on strings, lists,
   arrays, etc. *)

(** Mapping under pairs *)

val on_fst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
val on_snd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
val map_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b

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

(** {6 Empty type} *)

module Empty :
sig
  type t
  val abort : t -> 'a
end

(** {6 Strings. } *)

module String : CString.ExtS

(** Substitute %s in the first chain by the second chain *)
val subst_command_placeholder : string -> string -> string

(** {6 Lists. } *)

module List : CList.ExtS

val (@) : 'a list -> 'a list -> 'a list

(** {6 Arrays. } *)

module Array : CArray.ExtS

(** {6 Sets. } *)

module Set : module type of CSet

(** {6 Maps. } *)

module Map : module type of CMap

(** {6 Stacks.} *)

module Stack : module type of CStack

(** {6 Streams. } *)

val stream_nth : int -> 'a Stream.t -> 'a
val stream_njunk : int -> 'a Stream.t -> unit

(** {6 Matrices. } *)

val matrix_transpose : 'a list list -> 'a list list

(** {6 Functions. } *)

val identity : 'a -> 'a

(** Left-to-right function composition:
    
    [f1 %> f2] is [fun x -> f2 (f1 x)].

    [f1 %> f2 %> f3] is [fun x -> f3 (f2 (f1 x))].

    [f1 %> f2 %> f3 %> f4] is [fun x -> f4 (f3 (f2 (f1 x)))]

    etc.
*)
val ( %> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c

val const : 'a -> 'b -> 'a
val iterate : ('a -> 'a) -> int -> 'a -> 'a
val repeat : int -> ('a -> unit) -> 'a -> unit
val app_opt : ('a -> 'a) option -> 'a -> 'a

(** {6 Delayed computations. } *)

type 'a delayed = unit -> 'a

val delayed_force : 'a delayed -> 'a

(** {6 Enriched exceptions} *)

type iexn = Exninfo.iexn

val iraise : iexn -> 'a

(** {6 Misc. } *)

type ('a, 'b) union = ('a, 'b) CSig.union = Inl of 'a | Inr of 'b
(** Union type *)

module Union :
sig
  val map : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) union -> ('c, 'd) union
  val equal : ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> ('a, 'b) union -> ('a, 'b) union -> bool
  val fold_left : ('c -> 'a -> 'c) -> ('c -> 'b -> 'c) -> 'c -> ('a, 'b) union -> 'c
end

val map_union : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) union -> ('c, 'd) union
(** Alias for [Union.map] *)

type 'a until = 'a CSig.until = Stop of 'a | Cont of 'a
(** Used for browsable-until structures. *)

type ('a, 'b) eq = ('a, 'b) CSig.eq = Refl : ('a, 'a) eq

val sym : ('a, 'b) eq -> ('b, 'a) eq

val open_utf8_file_in : string -> in_channel
(** Open an utf-8 encoded file and skip the byte-order mark if any. *)

val set_temporary_memory : unit -> ('a -> 'a) * (unit -> 'a)
(** A trick which can typically be used to store on the fly the
   computation of values in the "when" clause of a "match" then
   retrieve the evaluated result in the r.h.s of the clause *)
