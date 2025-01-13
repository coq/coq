(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val get_interrupt_fname : int -> string
(** get filename used to pass interrupt pid on Win32 *)

val cvt_pid : (int -> int) ref
(* On Win32, convert OCaml "pid" (a handle) to a genuine Win32 pid *)
