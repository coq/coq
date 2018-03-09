(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coq
open Interface

class type ops =
object
  method go_to_insert : unit task
  method go_to_mark : GText.mark -> unit task
  method tactic_wizard : string list -> unit task
  method process_next_phrase : unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : unit task
  method raw_coq_query :
    route_id:int -> next:(query_rty value -> unit task) -> string -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
  method join_document : unit task
  method stop_worker : string -> unit task

  method get_n_errors : int
  method get_errors : (int * string) list
  method get_slaves_status : int * int * string CString.Map.t


  method handle_failure : handle_exn_rty -> unit task
  
  method destroy : unit -> unit
end

class coqops :
  Wg_ScriptView.script_view ->
  Wg_ProofView.proof_view ->
  Wg_RoutedMessageViews.message_views_router ->
  Wg_Segment.segment ->
  coqtop ->
  (unit -> string option) ->
  ops
