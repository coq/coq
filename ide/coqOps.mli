(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


class type ops =
object
  method go_to_insert : Coq.task
  method tactic_wizard : string list -> Coq.task
  method process_next_phrase : Coq.task
  method process_until_end_or_error : Coq.task
  method handle_reset_initial : Coq.reset_kind -> Coq.task
  method raw_coq_query : string -> Coq.task
  method show_goals : Coq.task
  method backtrack_last_phrase : Coq.task
  method include_file_dir_in_path : Coq.task
end

class coqops :
  Wg_ScriptView.script_view ->
  Wg_ProofView.proof_view ->
  Wg_MessageView.message_view ->
  (unit -> string option) ->
  ops
