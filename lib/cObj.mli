(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** {6 Physical size of an ocaml value.}

  These functions explore objects recursively and may allocate a lot. *)

val size : 'a -> int
(** Physical size of an object in words. *)

val size_b : 'a -> int
(** Same as [size] in bytes. *)

val size_kb : 'a -> int
(** Same as [size] in kilobytes. *)

(** {6 Logical size of an OCaml value *)

val obj_stats : 'a -> int * int * int
(** Return the (logical) value size, the string size, and the maximum depth of
    the object. This loops on cyclic structures. *)

(** {6 Total size of the allocated ocaml heap. } *)

val heap_size : unit -> int
(** Heap size, in words. *)

val heap_size_kb : unit -> int
(** Heap size, in kilobytes. *)
