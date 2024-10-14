(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type stack_t = (string * (string * int list) option) list
type vars_t = (string * Pp.t) list

class type debugger_view =
  object
    method coerce : GObj.widget
    method set_stack : stack_t -> unit
    method set_vars : vars_t -> unit
    method hide : unit -> unit
    method show : unit -> unit
    method set_forward_highlight_code : (string * int * int -> unit) -> unit
    method set_forward_clear_db_highlight : (unit -> unit) -> unit
    method set_forward_db_vars : (int -> unit) -> unit
    method set_forward_paned_pos : (int -> unit) -> unit
    method set_forward_get_basename : (unit -> string) -> unit
    method select_all : unit -> unit
  end

val debugger : string -> int -> debugger_view

val forward_keystroke : (Gdk.keysym * Gdk.Tags.modifier list -> int -> bool) ref
