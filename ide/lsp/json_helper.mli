open Yojson.Basic

val sub_from : string -> int -> string
val pmember : string -> t -> t
val uri_to_path : string -> string

type completion_context = { trigger_kind: int; trigger_char: string option }
val to_compl_context : t -> completion_context

type txdoc_item = { fname: string; langId: string; version: int; text: string }
val to_txdoc_item : t -> txdoc_item

type txdoc_pos = { path: string; line: int; col: int }
val to_txdoc_id : t -> string
val to_txdoc_pos : t -> txdoc_pos

type workspace_folder = { wk_uri: string; wk_name: string }
type wsch_event = { added: workspace_folder; removed: workspace_folder }
val to_wsch_event : t -> wsch_event
val to_contentch : t -> string

(* Report on server capabilities *)
val server_capabilities : t

type position = { line: int; character: int }
type range = { rng_start: position; rng_end: position }

(* Build a JSON diagnostic *)
val diag : string -> string -> range option -> t

(* Build an empty JSON diagnostic; used for clearing diagnostic *)
val diag_clear : string -> t
