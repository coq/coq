(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class command_window : string -> Coq.coqtop ->
  object
    method new_query : ?command:string -> ?term:string -> unit -> unit
    method pack_in : (GObj.widget -> unit) -> unit
    method refresh_font : unit -> unit
    method refresh_color : unit -> unit
    method show : unit
    method hide : unit
    method visible : bool
  end
