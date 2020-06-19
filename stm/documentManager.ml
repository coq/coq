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

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

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

type progress_hook = state option -> unit Lwt.t

let executed_ranges doc execution_state executed_loc =
  let valid_ids = List.map (fun s -> s.id) @@ Document.sentences_before doc executed_loc in
  let executed_ids = List.filter (ExecutionManager.is_executed execution_state) valid_ids in
  let remotely_executed_ids = List.filter (ExecutionManager.is_remotely_executed execution_state) valid_ids in
  List.map (Document.range_of_id doc) executed_ids,
  List.map (Document.range_of_id doc) remotely_executed_ids

let executed_ranges st =
  match st.executed_loc with
  | None -> [], []
  | Some loc ->
    executed_ranges st.document st.execution_state loc

let make_diagnostic doc id oloc message severity =
  let range =
    match oloc with
    | None -> range_of_id doc id
    | Some loc ->
      Document.range_of_loc doc loc
  in
  { range; message; severity }

let diagnostics st =
  let parse_errors = Document.parse_errors st.document in
  let exec_errors = ExecutionManager.errors st.execution_state in
  let mk_diag (id,oloc,message) =
    make_diagnostic st.document id oloc message Error
  in
  List.map mk_diag @@ parse_errors @ exec_errors

let init vernac_state document =
  let execution_state = ExecutionManager.init_master vernac_state in
  { document; execution_state; executed_loc = None }

let interpret_to_loc ~after ?(progress_hook=fun doc -> Lwt.return ()) state loc : (state * proof_data * 'a DelegationManager.events) Lwt.t =
  log @@ "[DM] Interpreting to loc " ^ string_of_int loc;
  let rec make_progress state =
    let open Lwt.Infix in
    let invalid_ids, document = validate_document state.document in
    Lwt_list.fold_left_s (fun st id ->
        ExecutionManager.invalidate (Document.schedule state.document) id st) state.execution_state (Stateid.Set.elements invalid_ids) >>= fun execution_state ->
    let state = { state with document; execution_state } in
    (*
    log @@ ParsedDoc.to_string doc.parsed_doc;
    log @@ Scheduler.string_of_schedule @@ ParsedDoc.schedule doc.parsed_doc;
    *)
    (** We jump to the sentence before the position, otherwise jumping to the
    whitespace at the beginning of a sentence will observe the state after
    executing the sentence, which is unnatural. *)
    let find = if after then find_sentence else find_sentence_before in
    match find state.document loc with
    | None -> (* document is empty *) Lwt.return (state, None, [])
    | Some { id; stop; start } ->
      let progress_hook st = progress_hook (Option.map (fun st -> { state with execution_state = st; executed_loc = Some stop }) st) in
      ExecutionManager.observe progress_hook state.document id state.execution_state >>= fun (st,actions) ->
      log @@ "[DM] Observed " ^ Stateid.to_string id;
      let state = { state with execution_state = st } in
      if Document.parsed_loc state.document < loc && Document.more_to_parse state.document then
        make_progress state
      else
      let executed_loc = Some stop in
      let proof_data = match ExecutionManager.get_proofview st id with
        | None -> None
        | Some pv -> let pos = Document.position_of_loc state.document stop in Some (pv, pos)
      in
      Lwt.return ({ state with executed_loc }, proof_data, actions)
  in
  make_progress state

let interpret_to_position ?progress_hook state pos =
  let loc = Document.loc_of_position state.document pos in
  interpret_to_loc ~after:false ?progress_hook state loc

let interpret_to_previous doc =
  match doc.executed_loc with
  | None -> Lwt.return (doc, None, [])
  | Some loc ->
    interpret_to_loc ~after:false doc (loc-1)

let interpret_to_next doc =
  match doc.executed_loc with
  | None -> Lwt.return (doc, None, [])
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
