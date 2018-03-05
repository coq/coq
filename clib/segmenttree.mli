(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module is a very simple implementation of "segment trees".

    A segment tree of type ['a t] represents a mapping from a union of
    disjoint segments to some values of type 'a. 
*)

(** A mapping from a union of disjoint segments to some values of type ['a]. *)
type 'a t

(** [make [(i1, j1), v1; (i2, j2), v2; ...]] creates a mapping that
    associates to every integer [x] the value [v1] if [i1 <= x <= j1],
    [v2] if [i2 <= x <= j2], and so one. 
    Precondition: the segments must be sorted. *)
val make : ((int * int) * 'a) list -> 'a t

(** [lookup k t] looks for an image for key [k] in the interval tree [t]. 
    Raise [Not_found] if it fails. *)
val lookup : int -> 'a t -> 'a


