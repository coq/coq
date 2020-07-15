(* camlp5r *)
(* ploc.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

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
