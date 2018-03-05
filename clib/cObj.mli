(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 Physical size of an ocaml value.}

  These functions explore objects recursively and may allocate a lot. *)

val size : 'a -> int
(** Physical size of an object in words. *)

val size_b : 'a -> int
(** Same as [size] in bytes. *)

val size_kb : 'a -> int
(** Same as [size] in kilobytes. *)

(** {6 Physical size of an ocaml value with sharing.} *)

(** This time, all the size of objects are computed with respect
    to a larger object containing them all, and we only count
    the new blocks not already seen earlier in the left-to-right
    visit of the englobing object. *)

(** Provides the global object in which we'll search shared sizes *)

val register_shared_size : 'a -> unit

(** Shared size (in word) of an object with respect to the global object
    given by the last [register_shared_size]. *)

val shared_size_of_obj : 'a -> int

(** Same, with an object indicated by its occurrence in the global
    object. The very same object could have a zero size or not, depending
    of the occurrence we're considering in the englobing object.
    For speaking of occurrences, we use an [int list] for a path
    of field indexes (leftmost = deepest block, rightmost = top block of the
    global object). *)

val shared_size_of_pos : int list -> int

(** {6 Logical size of an OCaml value.} *)

val obj_stats : 'a -> int * int * int
(** Return the (logical) value size, the string size, and the maximum depth of
    the object. This loops on cyclic structures. *)

(** {6 Total size of the allocated ocaml heap. } *)

val heap_size : unit -> int
(** Heap size, in words. *)

val heap_size_kb : unit -> int
(** Heap size, in kilobytes. *)
