(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

(* Old plain messages (used to be in Pp) *)
type level =
  | Debug of string
  | Info
  | Notice
  | Warning
  | Error

type message = {
  message_level : level;
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

(** {6 Feedback sent, even asynchronously, to the user interface} *)

(* This stuff should be available to most of the system, line msg_* above.
 * But I'm unsure this is the right place, especially for the global edit_id.
 *
 * Morally the parser gets a string and an edit_id, and gives back an AST.
 * Feedbacks during the parsing phase are attached to this edit_id.
 * The interpreter assignes an exec_id to the ast, and feedbacks happening
 * during interpretation are attached to the exec_id.
 * Only one among state_id and edit_id can be provided. *)

val set_feeder : (feedback -> unit) -> unit

val feedback :
  ?id:edit_or_state_id -> ?route:route_id -> feedback_content -> unit

val set_id_for_feedback : ?route:route_id -> edit_or_state_id -> unit
val get_id_for_feedback : unit -> edit_or_state_id * route_id


