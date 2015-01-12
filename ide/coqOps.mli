(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Coq

class type ops =
object
  method go_to_insert : unit task
  method go_to_mark : GText.mark -> unit task
  method tactic_wizard : string list -> unit task
  method process_next_phrase : unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : Coq.reset_kind -> unit task
  method raw_coq_query : string -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
  method join_document : unit task
  method stop_worker : string -> unit task

  method get_n_errors : int
  method get_errors : (int * string) list
  method get_slaves_status : int * int * string CString.Map.t


  method handle_failure : Interface.handle_exn_rty -> unit task
  
  method destroy : unit -> unit
end

class coqops :
  Wg_ScriptView.script_view ->
  Wg_ProofView.proof_view ->
  Wg_MessageView.message_view ->
  Wg_Segment.segment ->
  coqtop ->
  (unit -> string option) ->
  ops
