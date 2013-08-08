(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Purely functional streams}

  Contrarily to OCaml module [Stream], these are meant to be used purely
  functionally. This implies in particular that accessing an element does not
  discard it. *)

type +'a t
(** Type of pure streams. *)

(** {6 Constructors} *)

val empty : 'a t
(** The empty stream. *)

val cons : 'a -> 'a t -> 'a t
(** Append an element in front of a stream. *)

val thunk : 'a t Lazy.t -> 'a t
(** Internalize the lazyness of a stream. *)

(** {6 Destructors} *)

val is_empty : 'a t -> bool
(** Whethere a stream is empty. *)

val peek : 'a t -> ('a * 'a t) option
(** Return the head and the tail of a stream, if any. *)

(** {6 Standard operations}

    All stream-returning functions are lazy. The other ones are eager. *)

val app : 'a t -> 'a t -> 'a t
(** Append two streams. Not tail-rec. *)

val map : ('a -> 'b) -> 'a t -> 'b t
(** Mapping of streams. Not tail-rec. *)

val iter : ('a -> unit) -> 'a t -> unit
(** Iteration over streams. *)

val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
(** Fold over streams. *)

val concat : 'a t t -> 'a t
(** Appends recursively a stream of streams. *)

val map_filter : ('a -> 'b option) -> 'a t -> 'b t
(** Mixing [map] and [filter]. Not tail-rec. *)

(** {6 Conversions} *)

val of_list : 'a list -> 'a t
(** Convert a list into a stream. *)

val to_list : 'a t -> 'a list
(** Convert a stream into a list. *)

(** {6 Other}*)

val force : 'a t -> 'a t
(** Forces the whole stream. *)
