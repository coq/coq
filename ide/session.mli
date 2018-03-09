(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A session is a script buffer + proof + messages,
    interacting with a coqtop, and a few other elements around *)

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

type session = {
  buffer : GText.buffer;
  script : Wg_ScriptView.script_view;
  proof : Wg_ProofView.proof_view;
  messages : Wg_RoutedMessageViews.message_views_router;
  segment : Wg_Segment.segment;
  fileops : FileOps.ops;
  coqops : CoqOps.ops;
  coqtop : Coq.coqtop;
  command : Wg_Command.command_window;
  finder : Wg_Find.finder;
  tab_label : GMisc.label;
  errpage : errpage;
  jobpage : jobpage;
  mutable control : control;
}

(** [create filename coqtop_args] *)
val create : string option -> string list -> session

val kill : session -> unit

val build_layout : session ->
  GObj.widget option * GObj.widget option * GObj.widget
