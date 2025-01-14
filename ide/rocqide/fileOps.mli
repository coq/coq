(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val reload_timer : Ideutils.timer
val autosave_timer : Ideutils.timer

class type ops =
object
  method filename : string option
  method update_stats : unit
  method changed_on_disk : bool
  method reload : ?parent:GWindow.window -> unit -> unit
  method auto_save : unit
  method save : string -> bool
  method saveas : ?parent:GWindow.window -> string -> bool
end

class fileops : GText.buffer -> string option -> (unit -> unit) -> ops
