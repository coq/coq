(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Skewed lists

    This is a purely functional datastructure isomorphic to usual lists, except
    that it features a O(log n) lookup while preserving the O(1) cons operation.

*)

(** {5 Constructors} *)

type +'a t

val empty : 'a t
val cons : 'a -> 'a t -> 'a t

(** {5 List operations} *)

val is_empty : 'a t -> bool
val length : 'a t -> int
val map : ('a -> 'b) -> 'a t -> 'b t
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val hd : 'a t -> 'a
val tl : 'a t -> 'a t

val skipn : int -> 'a t -> 'a t

(** {5 Indexing operations} *)

val get : 'a t -> int -> 'a
