(* camlp5r *)
(* ploc.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Locations and some pervasive type and value. *)

type t

(* located exceptions *)

exception Exc of t * exn
   (** [Ploc.Exc loc e] is an encapsulation of the exception [e] with
       the input location [loc]. To be used to specify a location
       for an error. This exception must not be raised by [raise] but
       rather by [Ploc.raise] (see below), to prevent the risk of several
       encapsulations of [Ploc.Exc]. *)
val raise : t -> exn -> 'a
   (** [Ploc.raise loc e], if [e] is already the exception [Ploc.Exc],
       re-raise it (ignoring the new location [loc]), else raise the
       exception [Ploc.Exc loc e]. *)

(* making locations *)

val make_loc : string -> int -> int -> int * int -> string -> t
   (** [Ploc.make_loc fname line_nb bol_pos (bp, ep) comm] creates a location
       starting at line number [line_nb], where the position of the beginning
       of the line is [bol_pos] and between the positions [bp] (included) and
       [ep] excluded. And [comm] is the comment before the location. The
       positions are in number of characters since the begin of the stream. *)
val make_unlined : int * int -> t
   (** [Ploc.make_unlined] is like [Ploc.make] except that the line number
       is not provided (to be used e.g. when the line number is unknown. *)

val dummy : t
   (** [Ploc.dummy] is a dummy location, used in situations when location
       has no meaning. *)

(* getting location info *)

val file_name : t -> string
   (** [Ploc.file_name loc] returns the file name of the location. *)
val first_pos : t -> int
   (** [Ploc.first_pos loc] returns the position of the begin of the location
       in number of characters since the beginning of the stream. *)
val last_pos : t -> int
   (** [Ploc.last_pos loc] returns the position of the first character not
       in the location in number of characters since the beginning of the
       stream. *)
val line_nb : t -> int
   (** [Ploc.line_nb loc] returns the line number of the location or [-1] if
       the location does not contain a line number (i.e. built with
       [Ploc.make_unlined]. *)
val bol_pos : t -> int
   (** [Ploc.bol_pos loc] returns the position of the beginning of the line
       of the location in number of characters since the beginning of
       the stream, or [0] if the location does not contain a line number
       (i.e. built with [Ploc.make_unlined]. *)
val line_nb_last : t -> int
val bol_pos_last : t -> int
   (** Return the line number and the position of the beginning of the line
       of the last position. *)
val comment : t -> string
   (** [Ploc.comment loc] returns the comment before the location. *)
val comment_last : t -> string
   (** [Ploc.comment loc] returns the last comment of the location. *)

(* combining locations *)

val encl : t -> t -> t
   (** [Ploc.encl loc1 loc2] returns the location starting at the
       smallest start of [loc1] and [loc2] and ending at the greatest end
       of them. In other words, it is the location enclosing [loc1] and
       [loc2]. *)
val shift : int -> t -> t
   (** [Ploc.shift sh loc] returns the location [loc] shifted with [sh]
       characters. The line number is not recomputed. *)
val sub : t -> int -> int -> t
   (** [Ploc.sub loc sh len] is the location [loc] shifted with [sh]
       characters and with length [len]. The previous ending position
       of the location is lost. *)
val after : t -> int -> int -> t
   (** [Ploc.after loc sh len] is the location just after loc (starting at
       the end position of [loc]) shifted with [sh] characters and of length
       [len]. *)
val with_comment : t -> string -> t
   (** Change the comment part of the given location *)
