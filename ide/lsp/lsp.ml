open Yojson.Basic
open Yojson.Basic.Util

open Json_helper

type assoct = (string * t) list

let lsp_of_response (qid: int option) (response: t) : t =
  match qid with
  | Some i -> `Assoc ([("jsonrpc", `String "2.0"); ("id", `Int i)] @ (response |> to_assoc))
  (* In the case of a notification response, there is no query_id associated *)
  | None -> `Assoc ([("jsonrpc", `String "2.0")] @ (response |> to_assoc))

type lquery =
| Initialize of int * string
| Initialized
| Shutdown
| Exit
| Cancel of int
| FolderChange of wsch_event
| ChangeConfig
| ChangeWatch
| Symbol of string
| ExecCommand of string
| DidOpen of txdoc_item
| DidChange of string * string
| WillSave of string
| WillSaveWait of string
| DidSave of string * string
| DidClose of string
| Completion of txdoc_pos * completion_context
| Resolve
| Hover of txdoc_pos
| SignatureHelp of txdoc_pos
| Declaration of txdoc_pos
| Definition of txdoc_pos
| TypeDefinition of txdoc_pos
| Implementation of txdoc_pos
| References
| DocumentHighlight of txdoc_pos
| DocumentSymbol
| CodeAction
| CodeLens
| CodeLensResolve
| DocumentLink
| DocumentLinkResolve
| DocumentColor
| ColorPresentation
| Formatting
| RangeFormatting
| TypeFormatting
| Rename
| PrepareRename of txdoc_pos
| FoldingRange
| BadProtocolMsg of string

type lsp_query = { query_id: int option; q: lquery }

type error_code =
| MethodNotFound
| InternalError

let errorcode_to_int : error_code -> int = function
| MethodNotFound -> -32601
| InternalError -> -32603

(** For converting back into json **)
let response_err (err: error_code) (msg: string option) : t =
  match msg with
  | Some msg -> `Assoc [("code", `Int (errorcode_to_int err)); ("message", `String msg)]
  | None -> `Assoc [("code", `Int (errorcode_to_int err))]

let wrap_jsfail (qid: int option) (str: string) (js: t): lsp_query =
  { query_id = qid; q = BadProtocolMsg (str ^ "\n" ^ (pretty_to_string js)) }

let wrap_parse_err (str: string): lsp_query =
  { query_id = None; q = BadProtocolMsg str }

let unpack_lsp_query (r : t) : lsp_query =
  try
    let qid = member "id" r |> to_int in
    try
      { query_id = Some qid;
        q = match member "method" r |> to_string with
            | "initialize" -> Initialize (pmember "processId" r |> to_int,
                                          pmember "rootUri" r |> to_string)
            | "initialized" -> Initialized
            | "shutdown" -> Shutdown
            | "exit" -> Exit
            | "$/cancelRequest" -> Cancel (pmember "id" r |> to_int)
            | "workspace/didChangeWorkspaceFolders" -> FolderChange
                                                      (pmember "event" r |> to_wsch_event)
            | "workspace/didChangeConfiguration" -> ChangeConfig
            | "workspace/didChangeWatchedFiles" -> ChangeWatch
            | "workspace/symbol" -> Symbol (pmember "r" r |> to_string)
            | "workspace/executeCommand" -> ExecCommand
                                            (pmember "command" r |> to_string)
            | "textDocument/didOpen" -> DidOpen (pmember "textDocument" r |> to_txdoc_item)
            | "textDocument/didChange" -> DidChange (to_txdoc_id r,
                                                    pmember "contentChanges" r |> to_contentch)
            | "textDocument/willSave" -> WillSave (to_txdoc_id r)
            | "textDocument/willSaveWaitUntil" -> WillSaveWait (to_txdoc_id r)
            | "textDocument/didSave" -> DidSave (to_txdoc_id r, pmember "text" r |> to_string)
            | "textDocument/didClose" -> DidClose (to_txdoc_id r)
            | "textDocument/completion" -> Completion (to_txdoc_pos r,
                                                      pmember "context" r |> to_compl_context)
            | "completionItem/resolve" -> Resolve
            | "textDocument/hover" -> Hover (to_txdoc_pos r)
            | "textDocument/signatureHelp" -> SignatureHelp (to_txdoc_pos r)
            | "textDocument/declaration" -> Declaration (to_txdoc_pos r)
            | "textDocument/definition" -> Definition (to_txdoc_pos r)
            | "textDocument/typeDefinition" -> TypeDefinition (to_txdoc_pos r)
            | "textDocument/implementation" -> Implementation (to_txdoc_pos r)
            | "textDocument/references" -> References
            | "textDocument/documentHighlight" -> DocumentHighlight (to_txdoc_pos r)
            | "textDocument/documentSymbol" -> DocumentSymbol
            | "textDocument/codeAction" -> CodeAction
            | "textDocument/codeLens" -> CodeLens
            | "codeLens/resolve" -> CodeLensResolve
            | "textDocument/documentLink" -> DocumentLink
            | "documentLink/resolve" -> DocumentLinkResolve
            | "textDocument/documentColor" -> DocumentColor
            | "textDocument/colorPresentation" -> ColorPresentation
            | "textDocument/formatting" -> Formatting
            | "textDocument/rangeFormatting" -> RangeFormatting
            | "textDocument/onTypeFormatting" -> TypeFormatting
            | "textDocument/rename" -> Rename
            | "textDocument/prepareRename" -> PrepareRename (to_txdoc_pos r)
            | "textDocument/foldingRange" -> FoldingRange
            | m -> BadProtocolMsg (Printf.sprintf "Unknown method '%s'" m) }
        with
        | Type_error (str, js) -> wrap_jsfail (Some qid) str js
        | Undefined (str, js) -> wrap_jsfail (Some qid) str js
      with
      | Type_error (str, js) -> wrap_jsfail None str js
      | Undefined (str, js) -> wrap_jsfail None str js

(* The three kinds of responses *)
let resultResponse (r: t) : t option = Some (`Assoc [("result", r)])
let errorResponse (r: t) : t option = Some (`Assoc [("error", r)])
let nullResponse : t option = resultResponse `Null

type state_or_exit_t = State of Vernac.State.t | ExitCode of int
type response_state_t = t option * state_or_exit_t

let run_query (state: Vernac.State.t) (q: lquery) : response_state_t =
  try
    match q with
    | Initialize (_, _) -> resultResponse server_capabilities, State state
    | Initialized -> None, State state
    | Shutdown -> nullResponse, State state
    | Exit -> None, ExitCode 0
    | Cancel id -> None, State state
    | FolderChange evt -> nullResponse, State state
    | ChangeConfig -> nullResponse, State state
    | ChangeWatch -> None, State state
    | Symbol sym -> nullResponse, State state
    | ExecCommand cmd -> nullResponse, State state
    | DidOpen { fname = f; langId = _; version = _; text = t } -> nullResponse, State state
    | DidChange (txid, content) -> None, State state
    | WillSave txid -> None, State state
    | WillSaveWait txid -> nullResponse, State state
    | DidSave (f, t) -> nullResponse, State state
    | DidClose txid -> None, State state
    | Completion (txpos, ctx) -> nullResponse, State state
    | Resolve -> nullResponse, State state
    | Hover txpos -> nullResponse, State state
    | SignatureHelp txpos -> nullResponse, State state
    | Declaration txpos -> nullResponse, State state
    | Definition txpos -> nullResponse, State state
    | TypeDefinition txpos -> nullResponse, State state
    | Implementation txpos -> nullResponse, State state
    | References -> nullResponse, State state
    | DocumentHighlight txpos -> nullResponse, State state
    | DocumentSymbol -> nullResponse, State state
    | CodeAction -> nullResponse, State state
    | CodeLens -> nullResponse, State state
    | CodeLensResolve -> nullResponse, State state
    | DocumentLink -> nullResponse, State state
    | DocumentLinkResolve -> nullResponse, State state
    | DocumentColor -> nullResponse, State state
    | ColorPresentation -> nullResponse, State state
    | Formatting -> nullResponse, State state
    | RangeFormatting -> nullResponse, State state
    | TypeFormatting -> nullResponse, State state
    | Rename -> nullResponse, State state
    | PrepareRename txpos -> nullResponse, State state
    | FoldingRange -> nullResponse, State state
    | BadProtocolMsg msg -> errorResponse (response_err MethodNotFound (Some msg)), State state
  with
  | _ -> errorResponse (response_err InternalError None), State state

let rec parse_header_len (stream: string Stream.t) (len: int): int =
  let line = Stream.next stream in
  if String.starts_with ~prefix:"Content-Length: " line then
    parse_header_len stream (int_of_string (sub_from line 16))
  else if String.starts_with ~prefix:"Content-Type: " line then
    parse_header_len stream len
  else
    len

let read_lsp_query (stream: string Stream.t): lsp_query =
  match parse_header_len stream 0 with
  | n -> let str = Stream.npeek n stream in
         if List.length str != n then
           wrap_parse_err (Printf.sprintf "Could not read %d bytes" n)
         else
           unpack_lsp_query (from_string (List.fold_right (fun s1 s2 -> s1 ^ s2) str ""))
  | exception Stream.Failure -> wrap_parse_err "Malformed LSP header"

