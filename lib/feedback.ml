(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype
open Serialize

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
  | SlaveStatus of int * string
  | ProcessingInMaster
  | Goals of Loc.t * string
  | FileLoaded of string * string

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
       let n, s = to_pair to_int to_string ns in
       SlaveStatus(n,s)
  | "goals", [loc;s] -> Goals (to_loc loc, to_string s)
  | "fileloaded", [dirpath; filename] ->
       FileLoaded(to_string dirpath, to_string filename)
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
        [of_pair of_int of_string (n,s)]
  | Goals (loc,s) ->
      constructor "feedback_content" "goals" [of_loc loc;of_string s]
  | FileLoaded(dirpath, filename) ->
      constructor "feedback_content" "fileloaded" [
        of_string dirpath;
        of_string filename ]

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

