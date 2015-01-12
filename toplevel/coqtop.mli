(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The Coq main module. The following function [start] will parse the
   command line, print the banner, initialize the load path, load the input
   state, load the files given on the command line, load the ressource file,
   produce the output state if any, and finally will launch [Coqloop.loop]. *)

val init_toplevel : string list -> unit

val start : unit -> unit


(* For other toploops *)
val toploop_init : (string list -> string list) ref
val toploop_run : (unit -> unit) ref

