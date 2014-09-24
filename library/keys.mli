(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Globnames

val declare_keys : global_reference -> global_reference -> unit
(** Declare two keys as being equivalent. *)

val equiv_keys : global_reference -> global_reference -> bool
(** Check equivalence of keys. *)
