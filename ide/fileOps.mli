(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val revert_timer : Ideutils.timer
val autosave_timer : Ideutils.timer

class type ops =
object
  method filename : string option
  method update_stats : unit
  method changed_on_disk : bool
  method revert : unit
  method auto_save : unit
  method save : string -> bool
  method saveas : string -> bool
end

class fileops : GText.buffer -> string option -> (unit -> unit) -> ops
