(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class command_window :
  Coq.coqtop -> Preferences.pref ref ->
  object
    method new_command : ?command:string -> ?term:string -> unit -> unit
    method frame : GBin.frame
  end
