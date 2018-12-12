(* camlp5r *)
(* ploc.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* located exceptions *)

exception Exc of Loc.t * exn
   (** [Ploc.Exc loc e] is an encapsulation of the exception [e] with
       the input location [loc]. To be used to specify a location
       for an error. This exception must not be raised by [raise] but
       rather by [Ploc.raise] (see below), to prevent the risk of several
       encapsulations of [Ploc.Exc]. *)

val raise : Loc.t -> exn -> 'a
   (** [Ploc.raise loc e], if [e] is already the exception [Ploc.Exc],
       re-raise it (ignoring the new location [loc]), else raise the
       exception [Ploc.Exc loc e]. *)

val make_unlined : int * int -> Loc.t
   (** [Ploc.make_unlined] is like [Ploc.make] except that the line number
       is not provided (to be used e.g. when the line number is unknown. *)

val dummy : Loc.t
   (** [Ploc.dummy] is a dummy location, used in situations when location
       has no meaning. *)

(* combining locations *)

val sub : Loc.t -> int -> int -> Loc.t
   (** [Ploc.sub loc sh len] is the location [loc] shifted with [sh]
       characters and with length [len]. The previous ending position
       of the location is lost. *)

val after : Loc.t -> int -> int -> Loc.t
   (** [Ploc.after loc sh len] is the location just after loc (starting at
       the end position of [loc]) shifted with [sh] characters and of length
       [len]. *)

val with_comment : Loc.t -> string -> Loc.t
   (** Change the comment part of the given location *)
