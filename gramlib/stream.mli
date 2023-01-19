(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt       *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Streams and parsers. *)

type ('e,'a) t
(** The type of streams holding values of type ['a].
    Producing a new value needs an environment ['e]. *)

exception Failure
(** Raised by streams when trying to access beyond their end. *)

(** {1 Stream builders} *)

val from : ?offset:int -> ('e -> 'a option) -> ('e,'a) t
(** [Stream.from f] returns a stream built from the function [f]. To
    create a new stream element, the function [f] is called. The user
    function [f] must return either [Some <value>] for a value or
    [None] to specify the end of the stream. [offset] will initialize
    the stream [count] to start with [offset] consumed items, which is
    useful for some uses cases such as parsing resumption.
*)

val empty : unit -> ('e,'a) t
(** Return the stream holding the elements of the list in the same
   order. *)

val of_string : ?offset:int -> string -> (unit,char) t
(** Return the stream of the characters of the string parameter. If
    set. [offset] parameter is similar to [from]. *)

val of_channel : in_channel -> (unit,char) t
(** Return the stream of the characters read from the input channel. *)

(** {1 Predefined parsers} *)

val next : 'e -> ('e,'a) t -> 'a
(** Return the first element of the stream and remove it from the
   stream.
   @raise Stream.Failure if the stream is empty. *)

val is_empty : 'e -> ('e,'a) t -> bool
(** Return [true] if the stream is empty, else [false]. *)


(** {1 Useful functions} *)

val peek : 'e -> ('e,'a) t -> 'a option
(** Return [Some] of "the first element" of the stream, or [None] if
   the stream is empty. *)

val junk : 'e -> ('e,'a) t -> unit
(** Remove the first element of the stream, possibly unfreezing
   it before. *)

val count : ('e,'a) t -> int
(** Return the current count of the stream elements, i.e. the number
   of the stream elements discarded. *)

val npeek : 'e -> int -> ('e,'a) t -> 'a list
(** [npeek e n] returns the list of the [n] first elements of
   the stream, or all its remaining elements if less than [n]
   elements are available. *)

val nth : 'e -> int -> ('e,'a) t -> 'a

val njunk : 'e -> int -> ('e,'a) t -> unit

(**/**)
