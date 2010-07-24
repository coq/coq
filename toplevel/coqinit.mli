(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Initialization. *)

val set_debug : unit -> unit

val set_rcfile : string -> unit
val set_rcuser : string -> unit

val no_load_rc : unit -> unit
val load_rcfile : unit -> unit

val push_include : string * Names.dir_path -> unit
val push_rec_include : string * Names.dir_path -> unit

val init_load_path : unit -> unit
val init_library_roots : unit -> unit

val init_ocaml_path : unit -> unit
