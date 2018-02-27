(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Xml_datatype

type level =
  | Debug
  | Info
  | Notice
  | Warning
  | Error

type doc_id = int
type route_id = int

type feedback_content =
  | Processed
  | Incomplete
  | Complete
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  | AddedAxiom
  | GlobRef of Loc.t * string * string * string * string
  | GlobDef of Loc.t * string * string * string
  | FileDependency of string option * string
  | FileLoaded of string * string
  (* Extra metadata *)
  | Custom of Loc.t option * string * xml
  (* Generic messages *)
  | Message of level * Loc.t option * Pp.t

type feedback = {
  doc_id   : doc_id;            (* The document being concerned *)
  span_id  : Stateid.t;
  route    : route_id;
  contents : feedback_content;
}

(** Feeders *)
let feeders : (int, feedback -> unit) Hashtbl.t = Hashtbl.create 7

let add_feeder =
  let f_id = ref 0 in fun f ->
  incr f_id;
  Hashtbl.add feeders !f_id f;
  !f_id

let del_feeder fid = Hashtbl.remove feeders fid

let default_route = 0
let span_id    = ref Stateid.dummy
let doc_id     = ref 0
let feedback_route = ref default_route

let set_id_for_feedback ?(route=default_route) d i =
  doc_id := d;
  span_id := i;
  feedback_route := route

let warn_no_listeners = ref true
let feedback ?did ?id ?route what =
  let m = {
     contents = what;
     route    = Option.default !feedback_route route;
     doc_id   = Option.default !doc_id did;
     span_id  = Option.default !span_id id;
  } in
  if !warn_no_listeners && Hashtbl.length feeders = 0 then
    Format.eprintf "Warning, feedback message received but no listener to handle it!@\n%!";
  Hashtbl.iter (fun _ f -> f m) feeders

(* Logging messages *)
let feedback_logger ?loc lvl msg =
  feedback ~route:!feedback_route ~id:!span_id (Message (lvl, loc, msg))

let msg_info    ?loc x = feedback_logger ?loc Info x
let msg_notice  ?loc x = feedback_logger ?loc Notice x
let msg_warning ?loc x = feedback_logger ?loc Warning x
let msg_error   ?loc x = feedback_logger ?loc Error x
let msg_debug   ?loc x = feedback_logger ?loc Debug x

(* Helper for tools willing to understand only the messages *)
let console_feedback_listener fmt =
  let open Format in
  let pp_lvl fmt lvl = match lvl with
    | Error   -> fprintf fmt "Error: "
    | Info    -> fprintf fmt "Info: "
    | Debug   -> fprintf fmt "Debug: "
    | Warning -> fprintf fmt "Warning: "
    | Notice  -> fprintf fmt ""
  in
  let pp_loc fmt loc = let open Loc in match loc with
    | None     -> fprintf fmt ""
    | Some loc ->
      let where =
        match loc.fname with InFile f -> f | ToplevelInput -> "Toplevel input" in
      fprintf fmt "\"%s\", line %d, characters %d-%d:@\n"
        where loc.line_nb (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos) in
  let checker_feed (fb : feedback) =
  match fb.contents with
  | Processed   -> ()
  | Incomplete  -> ()
  | Complete    -> ()
  | ProcessingIn _ -> ()
  | InProgress _ -> ()
  | WorkerStatus (_,_) -> ()
  | AddedAxiom  -> ()
  | GlobRef (_,_,_,_,_) -> ()
  | GlobDef (_,_,_,_) -> ()
  | FileDependency (_,_) -> ()
  | FileLoaded (_,_) -> ()
  | Custom (_,_,_) -> ()
  | Message (lvl,loc,msg) ->
    fprintf fmt "@[%a@]%a@[%a@]\n%!" pp_loc loc pp_lvl lvl Pp.pp_with msg
  in checker_feed
