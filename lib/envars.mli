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
val docdir : unit -> string
val coqbin : string
val coqroot : string
(* coqpath is stored in reverse order, since that is the order it
 * gets added to the searc path *)
val xdg_config_home : string
val xdg_dirs : string list
val coqpath : string list

val camlbin : unit -> string
val camlp4bin : unit -> string
val camllib : unit -> string
val camlp4lib : unit -> string
