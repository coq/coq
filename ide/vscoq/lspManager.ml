(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

open Document
open DocumentManager
open Printer
open Lwt.Infix
open Lwt_err.Infix

module CompactedDecl = Context.Compacted.Declaration

let init_state : Vernacstate.t option ref = ref None
let get_init_state () =
  match !init_state with
  | Some st -> st
  | None -> CErrors.anomaly Pp.(str "Initial state not available")

let states : (string, DocumentManager.state) Hashtbl.t = Hashtbl.create 39
let doc_ids : (int, string) Hashtbl.t = Hashtbl.create 39

let fresh_doc_id =
  let doc_id = ref (-1) in
  fun () -> incr doc_id; !doc_id

let lsp_debug = CDebug.create ~name:"vscoq-lsp"

let log ~verbosity msg =
  if CDebug.get_debug_level "vscoq-lsp" >= verbosity then
  Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

(*let string_field name obj = Yojson.Basic.to_string (List.assoc name obj)*)

let read_request ic : Yojson.Basic.t Lwt.t =
  Lwt_io.read_line ic >!= fun header ->
  let scan_header = Scanf.Scanning.from_string header in
  try
  Scanf.bscanf scan_header "Content-Length: %d" (fun size ->
      let buf = Bytes.create size in
      (* Discard a second newline *)
      Lwt_io.read_line ic >!= fun _ ->
      Lwt_io.read_into_exactly ic buf 0 size >!= fun () ->
      Lwt.return @@ Bytes.to_string buf
    ) >>= fun obj_str ->
    log ~verbosity:2 @@ "received: " ^ obj_str;
  Lwt.return @@ Yojson.Basic.from_string obj_str
  with Scanf.Scan_failure _ as reraise ->
    let reraise = Exninfo.capture reraise in
    log ~verbosity:1 @@ "failed to decode header: " ^ header;
    Exninfo.iraise reraise

let output_json obj : unit Lwt.t =
  let msg  = Yojson.Basic.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  (* log @@ "sent: " ^ msg; *)
  Lwt_io.write Lwt_io.stdout s >!= fun () -> Lwt.return ()

let mk_notification ~event ~params = `Assoc ["jsonrpc", `String "2.0"; "method", `String event; "params", params]
let mk_response ~id ~result = `Assoc ["jsonrpc", `String "2.0"; "id", `Int id; "result", result]

let do_initialize ~id : unit Lwt.t =
  let capabilities = `Assoc [
    "textDocumentSync", `Int 2 (* Incremental *)
  ]
  in
  let result = `Assoc ["capabilities", capabilities] in
  output_json @@ mk_response ~id ~result

let parse_loc json =
  let open Yojson.Basic.Util in
  let line = json |> member "line" |> to_int in
  let char = json |> member "character" |> to_int in
  Position.{ line ; char }

let mk_loc Position.{ line; char } =
  `Assoc [
    "line", `Int line;
    "character", `Int char;
  ]

let mk_range Range.{ start; stop } =
  `Assoc [
    "start", mk_loc start;
    "end", mk_loc stop;
  ]

let publish_diagnostics uri doc : unit Lwt.t =
  let mk_severity lvl =
    let open Feedback in
    `Int (match lvl with
    | Error -> 1
    | Warning -> 2
    | Notice -> 3
    | Info -> 3
    | Debug -> 3
    )
  in
  let mk_diagnostic d =
    `Assoc [
      "range", mk_range d.range;
      "severity", mk_severity d.severity;
      "message", `String d.message;
    ]
  in
  let diagnostics = List.map mk_diagnostic @@ DocumentManager.diagnostics doc in
  let params = `Assoc [
    "uri", `String uri;
    "diagnostics", `List diagnostics;
  ]
  in
  output_json @@ mk_notification ~event:"textDocument/publishDiagnostics" ~params

let send_highlights uri doc : unit Lwt.t =
  let executed_ranges, incomplete_ranges = DocumentManager.executed_ranges doc in
  let executed_ranges = List.map mk_range executed_ranges in
  let incomplete_ranges = List.map mk_range incomplete_ranges in
  let params = `Assoc [
    "uri", `String uri;
    "stateErrorRange", `List [];
    "parsingRange", `List [];
    "processingRange", `List [];
    "incompleteRange", `List incomplete_ranges;
    "axiomRange", `List [];
    "processedRange", `List executed_ranges;
  ]
  in
  output_json @@ mk_notification ~event:"coqtop/updateHighlights" ~params

let mk_goal sigma g =
  let env = Goal.V82.env sigma g in
  let min_env = Environ.reset_context env in
  let id = Goal.uid g in
  let ccl =
    pr_letype_env ~goal_concl_style:true env sigma (Goal.V82.concl sigma g)
  in
  let mk_hyp d (env,l) =
    let d' = CompactedDecl.to_named_context d in
    let env' = List.fold_right Environ.push_named d' env in
    let ids, body, typ = match d with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, None, typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
      ids, Some c, typ
    in
  let ids = List.map (fun id -> `String (Names.Id.to_string id.Context.binder_name)) ids in
  let typ = pr_ltype_env env sigma typ in
    let hyp = `Assoc ([
      "identifiers", `List ids;
      "type", `String (Pp.string_of_ppcmds typ);
      "diff", `String "None";
    ] @ Option.cata (fun body -> ["body", `String (Pp.string_of_ppcmds @@ pr_lconstr_env ~inctx:true env sigma body)]) [] body) in
    (env', hyp :: l)
  in
  let (_env, hyps) =
    Context.Compacted.fold mk_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  `Assoc [
    "id", `Int (int_of_string id);
    "hypotheses", `List (List.rev hyps);
    "goal", `String (Pp.string_of_ppcmds ccl)
  ]


let mk_proofview loc Proof.{ goals; sigma } =
  let goals = List.map (mk_goal sigma) goals in
  let shelved = List.map (mk_goal sigma) (Evd.shelf sigma) in
  let given_up = List.map (mk_goal sigma) (Evar.Set.elements @@ Evd.given_up sigma) in
  `Assoc [
    "type", `String "proof-view";
    "goals", `List goals;
    "shelvedGoals", `List shelved;
    "abandonedGoals", `List given_up;
    "focus", mk_loc loc
  ]

let send_proofview uri doc : unit Lwt.t =
  match DocumentManager.get_current_proof doc with
  | None -> Lwt.return ()
  | Some (proofview, pos) ->
    let result = mk_proofview pos proofview in
    let params = `Assoc [
      "uri", `String uri;
      "proofview", result;
    ]
    in
    output_json @@ mk_notification ~event:"coqtop/updateProofview" ~params

let update_view uri st =
  send_highlights uri st >>= fun () ->
  send_proofview uri st >>= fun () ->
  publish_diagnostics uri st

let textDocumentDidOpen params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let text = textDocument |> member "text" |> to_string in
  let id = fresh_doc_id () in
  let doc = Document.create_document ~id text in
  Hashtbl.add doc_ids id uri;
  let st = DocumentManager.init (get_init_state ()) doc in
  Hashtbl.add states uri st;
  update_view uri st

let textDocumentDidChange params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let contentChanges = params |> member "contentChanges" |> to_list in
  let read_edit edit =
    let text = edit |> member "text" |> to_string in
    let range = edit |> member "range" in
    let start = range |> member "start" |> parse_loc in
    let stop = range |> member "end" |> parse_loc in
    Range.{ start; stop }, text
  in
  let textEdits = List.map read_edit contentChanges in
  let st = Hashtbl.find states uri in
  let st = DocumentManager.apply_text_edits st textEdits in
  Hashtbl.replace states uri st;
  update_view uri st

let textDocumentDidSave params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = DocumentManager.validate_document st in
  Hashtbl.replace states uri st;
  update_view uri st

let progress_hook uri () : unit Lwt.t =
  let st = Hashtbl.find states uri in
  update_view uri st

let coqtopInterpretToPoint ~id params : (string * DocumentManager.events) Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let loc = params |> member "location" |> parse_loc in
  let st = Hashtbl.find states uri in
  let progress_hook = progress_hook uri in
  DocumentManager.interpret_to_position ~progress_hook st loc >>= fun (st, events) ->
  Hashtbl.replace states uri st;
  update_view uri st >>= fun () ->
  Lwt.return (uri, events)

let coqtopStepBackward ~id params : (string * DocumentManager.events) Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  DocumentManager.interpret_to_previous st >>= fun (st, events) ->
  Hashtbl.replace states uri st;
  update_view uri st >>= fun () ->
  Lwt.return (uri,events)

let coqtopStepForward ~id params : (string * DocumentManager.events) Lwt.t =
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  DocumentManager.interpret_to_next st >>= fun (st, events) ->
  Hashtbl.replace states uri st;
  update_view uri st >>= fun () ->
  Lwt.return (uri,events)

let coqtopResetCoq ~id params : unit Lwt.t =
  let open Yojson.Basic.Util in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let st = DocumentManager.reset (get_init_state ()) st in
  Hashtbl.replace states uri st;
  update_view uri st

let coqtopInterpretToEnd ~id params : (string * DocumentManager.events) Lwt.t =
  let open Yojson.Basic.Util in
  let open Lwt.Infix in
  let uri = params |> member "uri" |> to_string in
  let st = Hashtbl.find states uri in
  let progress_hook = progress_hook uri in
  DocumentManager.interpret_to_end ~progress_hook st >>= fun (st, events) ->
  Hashtbl.replace states uri st;
  update_view uri st >>= fun () ->
  Lwt.return (uri,events)

type lsp_event = Request of Yojson.Basic.t

type event =
 | LspManagerEvent of lsp_event
 | DocumentManagerEvent of string * DocumentManager.event

type events = event Lwt.t list

let inject_dm_event uri x : event Lwt.t =
  x >>= fun e -> Lwt.return @@ DocumentManagerEvent(uri,e)

let inject_dm_events (uri,l) =
  Lwt.return @@ List.map (inject_dm_event uri) l

let dispatch_method ~id method_name params : events Lwt.t =
  let open Lwt.Infix in
  match method_name with
  | "initialize" -> do_initialize ~id >>= fun () -> Lwt.return []
  | "initialized" -> Lwt.return []
  | "textDocument/didOpen" -> textDocumentDidOpen params >>= fun () -> Lwt.return []
  | "textDocument/didChange" -> textDocumentDidChange params >>= fun () -> Lwt.return []
  | "textDocument/didSave" -> textDocumentDidSave params >>= fun () -> Lwt.return []
  | "coqtop/interpretToPoint" -> coqtopInterpretToPoint ~id params >>= inject_dm_events
  | "coqtop/stepBackward" -> coqtopStepBackward ~id params  >>= inject_dm_events
  | "coqtop/stepForward" -> coqtopStepForward ~id params  >>= inject_dm_events
  | "coqtop/resetCoq" -> coqtopResetCoq ~id params >>= fun () -> Lwt.return []
  | "coqtop/interpretToEnd" -> coqtopInterpretToEnd ~id params >>= inject_dm_events
  | _ -> log ~verbosity:1 @@ "Ignoring call to unknown method: " ^ method_name; Lwt.return []

let lsp () = [
  read_request Lwt_io.stdin >!= fun req ->
  log ~verbosity:2 "[T] UI req ready";
  Lwt.return @@ LspManagerEvent (Request req)
]

let handle_lsp_event = function
  | Request req ->
      let open Yojson.Basic.Util in
      let id = Option.default 0 (req |> member "id" |> to_int_option) in
      let method_name = req |> member "method" |> to_string in
      let params = req |> member "params" in
      log ~verbosity:1 @@ "[T] ui step: " ^ method_name;
      dispatch_method ~id method_name params >>= fun more_events ->
      Lwt.return @@ more_events @ lsp()

let pr_lsp_event = function
  | Request req ->
    Pp.str "Request"

let handle_event = function
  | LspManagerEvent e -> handle_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    begin match Hashtbl.find_opt states uri with
    | None ->
      log ~verbosity:1 @@ "[LSP] ignoring event on non-existing document";
      Lwt.return []
    | Some st ->
      DocumentManager.handle_event e st >>= fun (ost, events) ->
      begin match ost with
        | None -> Lwt.return ()
        | Some st->
          Hashtbl.replace states uri st;
          update_view uri st
      end >>= fun () ->
      inject_dm_events (uri, events)
    end

let pr_event = function
  | LspManagerEvent e -> pr_lsp_event e
  | DocumentManagerEvent (uri, e) ->
    DocumentManager.pr_event e

let handle_feedback feedback =
  let Feedback.{ doc_id; span_id; contents } = feedback in
  match Hashtbl.find_opt doc_ids doc_id with
  | None -> log ~verbosity:1 @@ "[LSP] ignoring feedback with doc_id = " ^ (string_of_int doc_id)
  | Some uri ->
    let st = Hashtbl.find states uri in
    let st = DocumentManager.handle_feedback span_id contents st in
    Hashtbl.replace states uri st (* TODO could we publish diagnostics here? *)

let init () =
  init_state := Some (Vernacstate.freeze_interp_state ~marshallable:false)


