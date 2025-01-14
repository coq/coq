(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A session is a script buffer + proof + messages,
    interacting with a rocqtop, and a few other elements around *)

class type ['a] page =
  object
    inherit GObj.widget
    method update : 'a -> unit
    method on_update : callback:('a -> unit) -> unit
    method data : 'a
  end

class type control =
  object
    method detach : unit -> unit
  end

type errpage = (int * string) list page
type jobpage = string CString.Map.t page

type breakpoint = {
  mark_id : string;
  mutable prev_byte_offset : int; (* UTF-8 byte offset for Rocq *)
  mutable prev_uni_offset : int;  (* unicode offset for GTK *)
}

type session = {
  buffer : GText.buffer;
  script : Wg_ScriptView.script_view;
  proof : Wg_ProofView.proof_view;
  messages : Wg_RoutedMessageViews.message_views_router;
  segment : Wg_Segment.segment;
  fileops : FileOps.ops;
  rocqops : RocqOps.ops;
  rocqtop : RocqDriver.rocqtop;
  command : Wg_Command.command_window;
  finder : Wg_Find.finder;
  debugger : Wg_Debugger.debugger_view;
  tab_label : GMisc.label;
  errpage : errpage;
  warnpage : errpage;
  jobpage : jobpage;
  sid : int;
  basename : string;
  mutable control : control;
  mutable abs_file_name : string option;
  mutable debug_stop_pt : (session * int * int) option;
  mutable breakpoints : breakpoint list;
  mutable last_db_goals : Pp.t
}

(** [create filename rocqtop_args] *)
val create : string option -> string list -> session

val to_abs_file_name : string -> string

val kill : session -> unit

val build_layout : session ->
  GObj.widget option * GObj.widget option * GObj.widget

val window_size : (int * int) ref
