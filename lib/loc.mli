(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {5 Basic types} *)

type source =
  | InFile of string
  | ToplevelInput

type t = {
  fname : source; (** filename or toplevel input *)
  line_nb : int; (** start line number *)
  bol_pos : int; (** position of the beginning of start line *)
  line_nb_last : int; (** end line number *)
  bol_pos_last : int; (** position of the beginning of end line *)
  bp : int; (** start position *)
  ep : int; (** end position *)
}

(** {5 Location manipulation} *)

(** This is inherited from CAMPL4/5. *)

val create : source -> int -> int -> int -> int -> t
(** Create a location from a filename, a line number, a position of the
    beginning of the line, a start and end position *)

val unloc : t -> int * int
(** Return the start and end position of a location *)

val make_loc : int * int -> t
(** Make a location out of its start and end position *)

val merge : t -> t -> t
val merge_opt : t option -> t option -> t option
(** Merge locations, usually generating the largest possible span *)

val finer : t option -> t option -> bool
(** Answers [true] when the first location is more defined, or, when
    both defined, included in the second one *)

val shift_loc : int -> int -> t -> t
(** [shift_loc loc n p] shifts the beginning of location by [n] and
    the end by [p]; it is assumed that the shifts do not change the
    lines at which the location starts and ends *)

(** {5 Located exceptions} *)

val add_loc : Exninfo.info -> t -> Exninfo.info
(** Adding location to an exception *)

val get_loc : Exninfo.info -> t option
(** Retrieving the optional location of an exception *)

val raise : ?loc:t -> exn -> 'a
(** [raise loc e] is the same as [Pervasives.raise (add_loc e loc)]. *)

(** {5 Objects with location information } *)

type 'a located = t option * 'a

val tag : ?loc:t -> 'a -> 'a located
(** Embed a location in a type *)

val map : ('a -> 'b) -> 'a located -> 'b located
(** Modify an object carrying a location *)
