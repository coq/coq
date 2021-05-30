(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extending streams with a (non-canonical) location function *)

type 'a t
val from : ?loc:Loc.t -> (int -> ('a * Loc.t) option) -> 'a t

(** Returning the loc of the last consumed element or the initial loc
    if no element is consumed *)
val current_loc : 'a t -> Loc.t

(** Returning the loc of the max visited element or the initial loc
    if no element is consumed *)
val max_peek_loc : 'a t -> Loc.t

(** Returning the loc starting after element [bp] (counting from 0)
    and spanning up to already peeked element at position [ep], under
    the assumption that [bp] <= [ep]; returns an empty interval if
    [bp] = [ep]; returns the empty initial interval if additionally
    [bp] = 0; fails if the elements have not been peeked yet *)
val interval_loc : int -> int -> 'a t -> Loc.t

(** Return location of an already peeked element at some position counting from 0;
    fails if the element has not been peeked yet *)
val get_loc : int -> 'a t -> Loc.t

(** Lifted usual function on streams *)

val count : 'a t -> int

val peek : 'a t -> 'a option

val npeek : int -> 'a t -> 'a list

val junk : 'a t -> unit
  (** consumes the next element if there is one *)

val next : 'a t -> 'a
  (** [next strm] returns and consumes the next element;
      raise [Stream.Failure] if the stream is empty *)

(** Other functions *)

val peek_nth : int -> 'a t -> 'a
  (** [peek_nth n strm] returns the nth element counting from 0 without
      consuming the stream; raises [Stream.Failure] if not enough
      elements *)
