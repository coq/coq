(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype
open Serialize

type message_level =
  | Debug of string
  | Info
  | Notice
  | Warning
  | Error

type message = {
  message_level : message_level;
  message_content : string;
}

let of_message_level = function
  | Debug s ->
      Serialize.constructor "message_level" "debug" [Xml_datatype.PCData s]
  | Info -> Serialize.constructor "message_level" "info" []
  | Notice -> Serialize.constructor "message_level" "notice" []
  | Warning -> Serialize.constructor "message_level" "warning" []
  | Error -> Serialize.constructor "message_level" "error" []
let to_message_level =
  Serialize.do_match "message_level" (fun s args -> match s with
  | "debug" -> Debug (Serialize.raw_string args)
  | "info" -> Info
  | "notice" -> Notice
  | "warning" -> Warning
  | "error" -> Error
  | _ -> raise Serialize.Marshal_error)

let of_message msg =
  let lvl = of_message_level msg.message_level in
  let content = Serialize.of_string msg.message_content in
  Xml_datatype.Element ("message", [], [lvl; content])
let to_message xml = match xml with
  | Xml_datatype.Element ("message", [], [lvl; content]) -> {
      message_level = to_message_level lvl;
      message_content = Serialize.to_string content }
  | _ -> raise Serialize.Marshal_error

let is_message = function
  | Xml_datatype.Element ("message", _, _) -> true
  | _ -> false


type edit_id = int
type state_id = Stateid.t
type edit_or_state_id = Edit of edit_id | State of state_id

type feedback_content =
  | AddedAxiom
  | Processed
  | Incomplete
  | Complete
  | GlobRef of Loc.t * string * string * string * string
  | GlobDef of Loc.t * string * string * string
  | ErrorMsg of Loc.t * string
  | InProgress of int
  | SlaveStatus of string * string
  | ProcessingInMaster
  | Goals of Loc.t * string
  | StructuredGoals of Loc.t * xml
  | FileLoaded of string * string
  | Message of message

type feedback = {
  id : edit_or_state_id;
  content : feedback_content;
}

let to_feedback_content = do_match "feedback_content" (fun s a -> match s,a with
  | "addedaxiom", _ -> AddedAxiom
  | "processed", _ -> Processed
  | "processinginmaster", _ -> ProcessingInMaster
  | "incomplete", _ -> Incomplete
  | "complete", _ -> Complete
  | "globref", [loc; filepath; modpath; ident; ty] ->
       GlobRef(to_loc loc, to_string filepath,
         to_string modpath, to_string ident, to_string ty)
  | "globdef", [loc; ident; secpath; ty] ->
       GlobDef(to_loc loc, to_string ident, to_string secpath, to_string ty)
  | "errormsg", [loc;  s] -> ErrorMsg (to_loc loc, to_string s)
  | "inprogress", [n] -> InProgress (to_int n)
  | "slavestatus", [ns] ->
       let n, s = to_pair to_string to_string ns in
       SlaveStatus(n,s)
  | "goals", [loc;s] -> Goals (to_loc loc, to_string s)
  | "structuredgoals", [loc;x]-> StructuredGoals (to_loc loc, x)
  | "fileloaded", [dirpath; filename] ->
       FileLoaded(to_string dirpath, to_string filename)
  | "message", [m] -> Message (to_message m)
  | _ -> raise Marshal_error)
let of_feedback_content = function
  | AddedAxiom -> constructor "feedback_content" "addedaxiom" []
  | Processed -> constructor "feedback_content" "processed" []
  | ProcessingInMaster -> constructor "feedback_content" "processinginmaster" []
  | Incomplete -> constructor "feedback_content" "incomplete" []
  | Complete -> constructor "feedback_content" "complete" []
  | GlobRef(loc, filepath, modpath, ident, ty) ->
      constructor "feedback_content" "globref" [
        of_loc loc;
        of_string filepath;
        of_string modpath;
        of_string ident;
        of_string ty ]
  | GlobDef(loc, ident, secpath, ty) ->
      constructor "feedback_content" "globdef" [
        of_loc loc;
        of_string ident;
        of_string secpath;
        of_string ty ]
  | ErrorMsg(loc, s) ->
      constructor "feedback_content" "errormsg" [of_loc loc; of_string s]
  | InProgress n -> constructor "feedback_content" "inprogress" [of_int n]
  | SlaveStatus(n,s) ->
      constructor "feedback_content" "slavestatus"
        [of_pair of_string of_string (n,s)]
  | Goals (loc,s) ->
      constructor "feedback_content" "goals" [of_loc loc;of_string s]
  | StructuredGoals (loc, x) ->
      constructor "feedback_content" "structuredgoals" [of_loc loc; x]
  | FileLoaded(dirpath, filename) ->
      constructor "feedback_content" "fileloaded" [
        of_string dirpath;
        of_string filename ]
  | Message m -> constructor "feedback_content" "message" [ of_message m ]

let of_edit_or_state_id = function
  | Edit id -> ["object","edit"], of_edit_id id
  | State id -> ["object","state"], Stateid.to_xml id

let of_feedback msg =
  let content = of_feedback_content msg.content in
  let obj, id = of_edit_or_state_id msg.id in
  Element ("feedback", obj, [id;content])
let to_feedback xml = match xml with
  | Element ("feedback", ["object","edit"], [id;content]) -> {
      id = Edit(to_edit_id id);
      content = to_feedback_content content }
  | Element ("feedback", ["object","state"], [id;content]) -> { 
      id = State(Stateid.of_xml id);
      content = to_feedback_content content }
  | _ -> raise Marshal_error

let is_feedback = function
  | Element ("feedback", _, _) -> true
  | _ -> false

