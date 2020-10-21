(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Document

let debug_dm = CDebug.create ~name:"document-manager"

let log msg =
  if CDebug.get_debug_level "document-manager" >= 1 then
  Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type proof_data = (Proof.data * Position.t) option

type diagnostic = {
  range : Range.t;
  message : string;
  severity : Feedback.level;
}

type state = {
  document : document;
  execution_state : ExecutionManager.state;
  observe_loc : int option; (* TODO materialize observed loc and line-by-line execution status *)
}

type event =
  | Execute of Vernacstate.t * ExecutionManager.prepared_task list
  | InterpretToLoc of int
  | ExecutionManagerEvent of ExecutionManager.event

type events = event Lwt.t list

type progress_hook = unit -> unit Lwt.t

let executed_ranges doc execution_state loc =
  let valid_ids = List.map (fun s -> s.id) @@ Document.sentences_before doc loc in
  let executed_ids = List.filter (ExecutionManager.is_executed execution_state) valid_ids in
  let remotely_executed_ids = List.filter (ExecutionManager.is_remotely_executed execution_state) valid_ids in
  List.map (Document.range_of_id doc) executed_ids,
  List.map (Document.range_of_id doc) remotely_executed_ids

let executed_ranges st =
  match st.observe_loc with
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
  let feedback = ExecutionManager.feedback st.execution_state in
  let mk_diag (id,lvl,oloc,msg) =
    make_diagnostic st.document id oloc msg lvl
  in
  let mk_error_diag (id,oloc,msg) = mk_diag (id,Feedback.Error,oloc,msg) in
  List.map mk_error_diag parse_errors @
    List.map mk_error_diag exec_errors @
    List.map mk_diag feedback

let init vernac_state document =
  let execution_state = ExecutionManager.init_master vernac_state in
  { document; execution_state; observe_loc = None }

let interpret_to_loc ?(progress_hook=fun doc -> Lwt.return ()) state loc : (state * events) Lwt.t =
    let open Lwt.Infix in
    let parsing_state_hook = ExecutionManager.get_parsing_state_after state.execution_state in
    let invalid_ids, document = validate_document ~parsing_state_hook state.document in
    Lwt_list.fold_left_s (fun st id ->
        ExecutionManager.invalidate (Document.schedule state.document) id st) state.execution_state (Stateid.Set.elements invalid_ids) >>= fun execution_state ->
    let state = { document; execution_state; observe_loc = Some loc } in
    (** We jump to the sentence before the position, otherwise jumping to the
    whitespace at the beginning of a sentence will observe the state after
    executing the sentence, which is unnatural. *)
    match find_sentence_before state.document loc with
    | None -> (* document is empty *) Lwt.return (state, [])
    | Some { id; stop; start } ->
      let progress_hook () = Lwt.return () in
      let vernac_st, (st, tasks) = ExecutionManager.build_tasks_for ~progress_hook state.document state.execution_state id in
      log @@ "[DM] Observed " ^ Stateid.to_string id;
      let state = { state with execution_state = st } in
      if Document.parsed_loc state.document < loc && Document.more_to_parse state.document then
        Lwt.return (state, List.map Lwt.return [Execute (vernac_st, tasks); InterpretToLoc loc])
      else
      (*
      let executed_loc = Some stop in
      let proof_data = match ExecutionManager.get_proofview st id with
        | None -> None
        | Some pv -> let pos = Document.position_of_loc state.document stop in Some (pv, pos)
      in
      *)
      (* TODO remove proof_data *)
      Lwt.return (state, [Lwt.return @@ Execute (vernac_st, tasks)])

(*
let interpret_to_loc ~after ?(progress_hook=fun doc -> Lwt.return ()) state loc : (state * proof_data * events) Lwt.t =
  log @@ "[DM] Interpreting to loc " ^ string_of_int loc;
  let rec make_progress state =
    let open Lwt.Infix in
    let parsing_state_hook = ExecutionManager.get_parsing_state_after state.execution_state in
    let invalid_ids, document = validate_document ~parsing_state_hook state.document in
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
    | None -> (* document is empty *) Lwt.return (state, None, []) (* FIXME don't we stop here if after=true and document is not fully parsed? *)
    | Some { id; stop; start } ->
      let progress_hook () = Lwt.return () in
      let st, tasks = ExecutionManager.build_tasks_for progress_hook state.document state.execution_state id in
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
      Lwt.return ({ state with executed_loc }, proof_data, [Execute tasks, executed_loc])
  in
  make_progress state
*)

let interpret_to_position ?progress_hook state pos =
  let loc = Document.loc_of_position state.document pos in
  interpret_to_loc ?progress_hook state loc

let interpret_to_previous doc =
  match doc.observe_loc with
  | None -> Lwt.return (doc, [])
  | Some loc ->
    interpret_to_loc doc (loc-1)

let interpret_to_next doc = Lwt.return (doc, []) (* TODO
  match doc.executed_loc with
  | None -> Lwt.return (doc, None, [])
  | Some stop ->
    interpret_to_after_loc doc (stop+1)
    *)

let interpret_to_end ?progress_hook state =
  interpret_to_loc ?progress_hook state (Document.end_loc state.document)

let reset vernac_st state =
  init vernac_st state.document

let retract state loc =
  let observe_loc = Option.map (fun loc' -> min loc loc') state.observe_loc in
  { state with observe_loc }

let apply_text_edits state edits =
  let document = apply_text_edits state.document edits in
  let state = { state with document } in
  retract state (Document.parsed_loc document)

let validate_document state =
  let parsing_state_hook = ExecutionManager.get_parsing_state_after state.execution_state in
  let invalid_ids, document = validate_document ~parsing_state_hook state.document in
  { state with document }

let handle_feedback state_id contents state =
  let open Feedback in
  match contents with
  | Message(level,loc,pp) ->
    let execution_state = ExecutionManager.handle_feedback state_id contents state.execution_state in
    { state with execution_state}
  | AddedAxiom -> state
  (* These 4 constructors are used to store the mappings for name resolution *)
  | GlobRef _ -> state
  | GlobDef _ -> state
  | FileDependency _ -> state
  | FileLoaded _ -> state
  (* Custom is used by plugins like Ltac (profiler, debugger) *)
  | Custom(_,_,_) -> state
  | _ -> state

let inject_em_event x = Lwt.Infix.(x >>= fun e -> Lwt.return @@ ExecutionManagerEvent e)
let inject_em_events events = List.map inject_em_event events

let handle_event ev st =
  let open Lwt.Infix in
  match ev with
  | Execute (vernac_st, []) ->
    (* We update the state to trigger a publication of diagnostics *)
    Lwt.return (Some st, [])
  | Execute (vernac_st, task :: tasks) ->
    let doc_id = Document.id_of_doc st.document in
    ExecutionManager.execute ~doc_id st.execution_state (vernac_st, [], false) task >>= fun (vernac_st,events,interrupted) ->
    (* We do not update the state here because we may have received feedback while
       executing *)
    Lwt.return (None, inject_em_events events @ [Lwt.return @@ Execute(vernac_st,tasks)])
  | InterpretToLoc loc ->
    interpret_to_loc st loc >>= fun (st, events) ->
      Lwt.return (Some st, events)
  | ExecutionManagerEvent ev ->
    ExecutionManager.handle_event ev >>= fun events ->
      Lwt.return (None, inject_em_events events)

let get_current_proof st =
  match Option.bind st.observe_loc (Document.find_sentence_before st.document) with
  | None -> None
  | Some sentence ->
    let pos = Document.position_of_loc st.document sentence.stop in
    match ExecutionManager.get_proofview st.execution_state sentence.id with
    | None -> None
    | Some pv -> Some (pv, pos)

let pr_event = function
| ExecuteToLoc _ -> Pp.str "ExecuteToLoc"
| ExecutionManagerEvent ev -> ExecutionManager.pr_event ev
