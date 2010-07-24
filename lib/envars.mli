(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file gathers environment variables needed by Coq to run (such
   as coqlib) *)

val coqlib : unit -> string
val coqbin : unit -> string

val camlbin : unit -> string
val camlp4bin : unit -> string
val camllib : unit -> string
val camlp4lib : unit -> string
