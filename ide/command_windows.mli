(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

class command_window :
  unit ->
  object
    method new_command : ?command:string -> ?term:string -> unit -> unit
    method frame : GBin.frame
  end

 val main : unit -> unit

val command_window : unit -> command_window


