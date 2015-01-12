(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

(* Old plain messages (used to be in Pp) *)
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

val of_message : message -> xml
val to_message : xml -> message
val is_message : xml -> bool


(** Coq "semantic" infos obtained during parsing/execution *)
type edit_id = int
type state_id = Stateid.t
type edit_or_state_id = Edit of edit_id | State of state_id
type route_id = int

val default_route : route_id

type feedback_content =
  (* STM mandatory data (must be displayed) *)
  | Processed
  | Incomplete
  | Complete
  | ErrorMsg of Loc.t * string
  (* STM optional data *)
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  (* Generally useful metadata *)
  | Goals of Loc.t * string
  | AddedAxiom
  | GlobRef of Loc.t * string * string * string * string
  | GlobDef of Loc.t * string * string * string
  | FileDependency of string option * string
  | FileLoaded of string * string
  (* Extra metadata *)
  | Custom of Loc.t * string * xml
  (* Old generic messages *)
  | Message of message

type feedback = {
  id : edit_or_state_id;       (* The document part concerned *)
  contents : feedback_content;  (* The payload *)
  route : route_id;            (* Extra routing info *)
}

val of_feedback : feedback -> xml
val to_feedback : xml -> feedback
val is_feedback : xml -> bool

