(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Basic types} *)

type t = {
  fname : string; (** filename *)
  line_nb : int; (** start line number *)
  bol_pos : int; (** position of the beginning of start line *)
  line_nb_last : int; (** end line number *)
  bol_pos_last : int; (** position of the beginning of end line *)
  bp : int; (** start position *)
  ep : int; (** end position *)
}

(** {5 Location manipulation} *)

(** This is inherited from CAMPL4/5. *)

val create : string -> int -> int -> int -> int -> t
(** Create a location from a filename, a line number, a position of the
    beginning of the line, a start and end position *)

val unloc : t -> int * int
(** Return the start and end position of a location *)

val make_loc : int * int -> t
(** Make a location out of its start and end position *)

val ghost : t
(** Dummy location *)

val is_ghost : t -> bool
(** Test whether the location is meaningful *)

val merge : t -> t -> t

(** {5 Located exceptions} *)

val add_loc : Exninfo.info -> t -> Exninfo.info
(** Adding location to an exception *)

val get_loc : Exninfo.info -> t option
(** Retrieving the optional location of an exception *)

val raise : ?loc:t -> exn -> 'a
(** [raise loc e] is the same as [Pervasives.raise (add_loc e loc)]. *)

(** {5 Objects with location information } *)

type 'a located = t * 'a
(** Embed a location in a type *)

(** Warning, this API is experimental  *)

val to_pair : 'a located -> t * 'a
val tag : ?loc:t -> 'a -> 'a located
val obj : 'a located -> 'a

val with_loc : (loc:t -> 'a -> 'b) -> 'a located -> 'b
val with_unloc : ('a -> 'b) -> 'a located -> 'b

val map : ('a -> 'b) -> 'a located -> 'b located
val map_with_loc : (loc:t -> 'a -> 'b) -> 'a located -> 'b located

val located_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b located -> 'a
val down_located : ('a -> 'b) -> 'a located -> 'b

(* Current not used *)
val located_iter2 : ('a -> 'b -> unit) -> 'a located -> 'b located -> unit

(** Projects out a located object *)

(** {5 Backward compatibility} *)

val dummy_loc : t
(** Same as [ghost] *)

val join_loc : t -> t -> t
(** Same as [merge] *)
