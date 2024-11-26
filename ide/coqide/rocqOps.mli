(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open RocqDriver
open Interface

class type ops =
object
  method go_to_insert : unit task
  method go_to_mark : GText.mark -> unit task
  method process_next_phrase : unit task
  method process_db_cmd : string ->
    next:(Interface.db_cmd_rty Interface.value -> unit task) -> unit task
  method process_db_configd : unit ->
    next:(Interface.db_configd_rty Interface.value -> unit task) -> unit task
  method process_db_upd_bpts : ((string * int) * bool) list ->
    next:(Interface.db_upd_bpts_rty Interface.value -> unit task) -> unit task
  method process_db_continue : db_continue_opt ->
    next:(Interface.db_continue_rty Interface.value -> unit task) -> unit task
  method process_db_stack :
    next:(Interface.db_stack_rty Interface.value -> unit task) -> unit task
  method process_db_vars : int ->
    next:(Interface.db_vars_rty Interface.value -> unit task) -> unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : unit task
  method raw_rocq_query :
    route_id:int -> next:(query_rty value -> unit task) -> string -> unit task
  method proof_diff : GText.mark -> next:(Pp.t value -> unit task) -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
  method join_document : unit task
  method stop_worker : string -> unit task

  method get_n_errors : int
  method get_errors : (int * string) list
  method get_warnings : (int * string) list
  method get_slaves_status : int * int * string CString.Map.t
  method backtrack_to_begin : unit -> unit task
  method handle_failure : handle_exn_rty -> unit task

  method destroy : unit -> unit
  method scroll_to_start_of_input : unit -> unit
  method set_forward_clear_db_highlight : (unit -> unit) -> unit
  method set_forward_set_goals_of_dbg_session : (Pp.t -> unit) -> unit
  method set_forward_init_db : (unit -> unit) -> unit
  method set_debug_goal : Pp.t -> unit
end

class rocqops :
  Wg_ScriptView.script_view ->
  Wg_ProofView.proof_view ->
  Wg_RoutedMessageViews.message_views_router ->
  Wg_Segment.segment ->
  rocqtop ->
  (unit -> string option) ->
  ops
