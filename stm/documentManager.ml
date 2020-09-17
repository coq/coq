(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Scheduler
open Document

let log msg = Format.eprintf "@[%s@]@\n%!" msg

type proof_data = (Proof.data * Position.t) option

type severity =
  | Warning
  | Error

type diagnostic = {
  range : Range.t;
  message : string;
  severity : severity;
}

type state = {
  document : document;
  execution_state : ExecutionManager.state;
  executed_loc : int option;
}

type progress_hook = state -> unit Lwt.t


(*
let executed_ranges doc =
  match doc.executed_loc with
  | None -> []
  | Some loc ->
    ParsedDoc.executed_ranges doc.raw_doc doc.parsed_doc doc.execution_state loc
    *)

(*
let diagnostics doc =
  let exec_errors = ExecutionManager.errors doc.execution_state in
  log @@ "exec errors in diags: " ^ string_of_int (List.length exec_errors);
  let mk_exec_diag (id,oloc,message) =
    ParsedDoc.make_diagnostic doc.raw_doc doc.parsed_doc id oloc message Error
  in
  let exec_diags = List.map mk_exec_diag exec_errors in
  ParsedDoc.parse_errors doc.raw_doc doc.parsed_doc @ exec_diags
  *)


let init vernac_state document =
  let execution_state = ExecutionManager.init vernac_state in
  { document; execution_state; executed_loc = None }

let interpret_to_loc ~after ?(progress_hook=fun doc -> Lwt.return ()) state loc : (state * proof_data) Lwt.t =
  log @@ "Interpreting to loc " ^ string_of_int loc;
  let rec make_progress state =
    let open Lwt.Infix in
    let invalid_ids, document = validate_document state.document in
    let state = { state with document } in (* FIXME invalidate invalid_ids *)
    (*
    log @@ ParsedDoc.to_string doc.parsed_doc;
    log @@ Scheduler.string_of_schedule @@ ParsedDoc.schedule doc.parsed_doc;
    *)
    (** We jump to the sentence before the position, otherwise jumping to the
    whitespace at the beginning of a sentence will observe the state after
    executing the sentence, which is unnatural. *)
    let find = if after then find_sentence else find_sentence_before in
    match find state.document loc with
    | None -> (* document is empty *) Lwt.return (state, None)
    | Some { id; stop; start } ->
      let progress_hook st = progress_hook { state with execution_state = st; executed_loc = Some stop } in
      ExecutionManager.observe progress_hook (Document.schedule state.document) id state.execution_state >>= fun st ->
      log @@ "Observed " ^ Stateid.to_string id;
      let state = { state with execution_state = st } in
      if Document.parsed_loc state.document < loc && Document.more_to_parse state.document then
        make_progress state
      else
      let executed_loc = Some stop in
      let proof_data = match ExecutionManager.get_proofview st id with
        | None -> None
        | Some pv -> let pos = Document.position_of_loc state.document stop in Some (pv, pos)
      in
      Lwt.return ({ state with executed_loc }, proof_data)
  in
  make_progress state

let interpret_to_position ?progress_hook state pos =
  let loc = Document.loc_of_position state.document pos in
  interpret_to_loc ~after:false ?progress_hook state loc

let interpret_to_previous doc =
  match doc.executed_loc with
  | None -> Lwt.return (doc, None)
  | Some loc ->
    interpret_to_loc ~after:false doc (loc-1)

let interpret_to_next doc =
  match doc.executed_loc with
  | None -> Lwt.return (doc, None)
  | Some stop ->
    interpret_to_loc ~after:true doc (stop+1)

let interpret_to_end ?progress_hook state =
  interpret_to_loc ~after:false ?progress_hook state (Document.end_loc state.document)

let reset vernac_st state =
  init vernac_st state.document

let apply_text_edits state edits =
  { state with document = apply_text_edits state.document edits }

let validate_document state =
  let invalid_ids, document = validate_document state.document in
  { state with document }
