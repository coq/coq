(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

(* Legacy-style logging messages (used to be in Pp) *)
type level =
  | Debug
  | Info
  | Notice
  | Warning
  | Error

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
  (* STM optional data *)
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  (* Generally useful metadata *)
  | AddedAxiom
  | GlobRef of Loc.t * string * string * string * string
  | GlobDef of Loc.t * string * string * string
  | FileDependency of string option * string
  | FileLoaded of string * string
  (* Extra metadata *)
  | Custom of Loc.t * string * xml
  (* Generic messages *)
  | Message of level * Loc.t option * Pp.std_ppcmds

type feedback = {
  id       : edit_or_state_id;  (* The document part concerned *)
  contents : feedback_content;  (* The payload *)
  route    : route_id;          (* Extra routing info *)
}

(** {6 Feedback sent, even asynchronously, to the user interface} *)
(* Morally the parser gets a string and an edit_id, and gives back an AST.
 * Feedbacks during the parsing phase are attached to this edit_id.
 * The interpreter assignes an exec_id to the ast, and feedbacks happening
 * during interpretation are attached to the exec_id.
 * Only one among state_id and edit_id can be provided. *)

(** [add_feeder f] adds a feeder listiner [f], returning its id *)
val add_feeder : (feedback -> unit) -> int

(** [del_feeder fid] removes the feeder with id [fid] *)
val del_feeder : int -> unit

(** Prints feedback messages of kind Message(Debug,_) using msg_debug *)
val debug_feeder : feedback -> unit

(** [feedback ?id ?route fb] produces feedback fb, with [route] and
    [id] set appropiatedly, if absent, it will use the defaults set by
    [set_id_for_feedback] *)
val feedback :
  ?id:edit_or_state_id -> ?route:route_id -> feedback_content -> unit

(** [set_id_for_feedback route id] Set the defaults for feedback *)
val set_id_for_feedback : ?route:route_id -> edit_or_state_id -> unit

(** {6 output functions}

[msg_notice] do not put any decoration on output by default. If
possible don't mix it with goal output (prefer msg_info or
msg_warning) so that interfaces can dispatch outputs easily. Once all
interfaces use the xml-like protocol this constraint can be
relaxed. *)
(* Should we advertise these functions more? Should they be the ONLY
   allowed way to output something? *)

val msg_info : ?loc:Loc.t -> Pp.std_ppcmds -> unit
(** Message that displays information, usually in verbose mode, such as [Foobar
    is defined] *)

val msg_notice : ?loc:Loc.t -> Pp.std_ppcmds -> unit
(** Message that should be displayed, such as [Print Foo] or [Show Bar]. *)

val msg_warning : ?loc:Loc.t -> Pp.std_ppcmds -> unit
(** Message indicating that something went wrong, but without serious
    consequences. *)

val msg_error : ?loc:Loc.t -> Pp.std_ppcmds -> unit
(** Message indicating that something went really wrong, though still
    recoverable; otherwise an exception would have been raised. *)

val msg_debug : ?loc:Loc.t -> Pp.std_ppcmds -> unit
(** For debugging purposes *)
