(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** A native integer module with usual utility functions. *)

type t = int

external equal : t -> t -> bool = "%eq"

external compare : t -> t -> int = "caml_int_compare"

val hash : t -> int
