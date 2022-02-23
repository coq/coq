open Yojson.Basic
open Yojson.Basic.Util

let pmember (k: string) (r: t): t =
  member "params" r |> member k

let sub_from (str: string) (pos: int) : string =
  String.sub str pos (String.length str - pos)

(** UNIX paths: "file:///foo/bar" corresponds to /foo/bar
    Windows paths: "file:///z%3A/foo" corresponds to z:/foo **)
let uri_to_path u = if String.sub u 9 3 = "%3A" then
                    Printf.sprintf "%s:%s" (String.sub u 8 1) (sub_from u 12)
                    else sub_from u 7
let path_to_uri u = if u.[1] = ':' then
                      let s = sub_from u 2 in
                      let rest = String.map (fun character -> if character == '\\' then '/' else character) s in
                      "file:///" ^ (String.sub u 0 1) ^ "%3A" ^ rest
                    else
                      "file://" ^ u

type completion_context = { trigger_kind: int; trigger_char: string option }
let to_compl_context (j: t) : completion_context =
  { trigger_kind = member "triggerKind" j |> to_int;
    trigger_char =
    match member "triggerChar" j |> to_string with
    | character -> Some character
    | exception _ -> None; }

type txdoc_item = { fname: string; langId: string; version: int; text: string }
let to_txdoc_item (j: t) : txdoc_item =
  { fname = member "uri" j |> to_string |> uri_to_path;
    langId = member "languageId" j |> to_string;
    version = member "version" j |> to_int;
    text = member "text" j |> to_string }

type txdoc_pos = { path: string; line: int; col: int }

(* Argument is of the form { "textDocument" : {"uri" : ... } } *)
let to_txdoc_id (r: t) : string =
  member "textDocument" r |> member "uri" |> to_string |> uri_to_path

(* Argument is of the form { "textDocument" : ...,
                             "position" : { "line" : ..., "character" : ... } } *)
let to_txdoc_pos (r: t) : txdoc_pos =
  let pos = pmember "position" r in
  { path = to_txdoc_id r;
    line = pos |> member "line" |> to_int;
     col = pos |> member "character" |> to_int }

type workspace_folder = { wk_uri: string; wk_name: string }
type wsch_event = { added: workspace_folder; removed: workspace_folder }
let to_wsch_event (j: t) : wsch_event =
  { added = { wk_uri = member "added" j |> member "uri" |> to_string;
              wk_name = member "added" j |> member "name" |> to_string };
    removed = { wk_uri = member "removed" j |> member "uri" |> to_string;
                wk_name = member "removed" j |> member "name" |> to_string } }

let to_contentch (j: t) : string =
  member "text" j |> to_string

type position = { line: int; character: int }
type range = { rng_start: position; rng_end: position }

let server_capabilities : t =
  `Assoc [("capabilities",
              `Assoc [("textDocumentSync", `Assoc [
                ("openClose", `Bool true);
                ("change", `Int 1);
                ("willSave", `Bool false);
                ("willSaveWaitUntil", `Bool false);
                ("save", `Assoc [("includeText", `Bool true)])]);
              ("hoverProvider", `Bool true);
              ("completionProvider", `Assoc []);
              ("signatureHelpProvider", `Assoc []);
              ("definitionProvider", `Bool true);
              ("typeDefinitionProvider", `Bool false);
              ("implementationProvider", `Bool false);
              ("referencesProvider", `Bool false);
              ("documentSymbolProvider", `Bool false);
              ("workspaceSymbolProvider", `Bool false);
              ("codeActionProvider", `Bool false)])]

let from_position (p: position) : t = `Assoc [("line", `Int p.line);
                                              ("character", `Int p.character)]

let from_range (r: range) : t =
  `Assoc [("start", from_position r.rng_start); ("end", from_position r.rng_end)]

let dummyrange : t =
  from_range { rng_start = { line = 0; character = 0; };
               rng_end = { line = 0; character = 0; }; }

let diag (fname: string) (msg: string) (r: range option) : t =
  let r' = match r with
           | Some r -> from_range r
           | None -> dummyrange in
  `Assoc [("method", `String "textDocument/publishDiagnostics");
          ("params", `Assoc [("uri", `String (path_to_uri fname));
                             ("diagnostics",
                              `List [`Assoc [("range", r'); ("message", `String msg)]])])]

let diag_clear (fname: string) : t =
  `Assoc [("method", `String "textDocument/publishDiagnostics");
          ("params", `Assoc [("uri", `String (path_to_uri fname)); ("diagnostics", `List [])])]
