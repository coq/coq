(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Basic types} *)

type t

type 'a located = t * 'a
(** Embed a location in a type *)

(** {5 Location manipulation} *)

(** This is inherited from CAMPL4/5. *)

val create : string -> int -> int -> (int * int) -> t
(** Create a location from a filename, a line number, a position of the
    beginning of the line and a pair of start and end position *)

val unloc : t -> int * int
(** Return the start and end position of a location *)

val make_loc : int * int -> t
(** Make a location out of its start and end position *)

val ghost : t
(** Dummy location *)

val is_ghost : t -> bool
(** Test whether the location is meaningful *)

val merge : t -> t -> t

val represent : t -> (string * int * int * int * int)
(** Return the arguments given in [create] *)

(** {5 Located exceptions} *)

val add_loc : Exninfo.info -> t -> Exninfo.info
(** Adding location to an exception *)

val get_loc : Exninfo.info -> t option
(** Retrieving the optional location of an exception *)

val raise : t -> exn -> 'a
(** [raise loc e] is the same as [Pervasives.raise (add_loc e loc)]. *)

(** {5 Location utilities} *)

val located_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b located -> 'a
val located_iter2 : ('a -> 'b -> unit) -> 'a located -> 'b located -> unit

val down_located : ('a -> 'b) -> 'a located -> 'b
(** Projects out a located object *)

(** {5 Backward compatibility} *)

val dummy_loc : t
(** Same as [ghost] *)

val join_loc : t -> t -> t
(** Same as [merge] *)
