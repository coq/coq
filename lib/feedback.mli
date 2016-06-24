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
  | Message of level * Richpp.richpp

type feedback = {
  id       : edit_or_state_id;  (* The document part concerned *)
  contents : feedback_content;  (* The payload *)
  route    : route_id;          (* Extra routing info *)
}

(** {6 Feedback sent, even asynchronously, to the user interface} *)

(** Moved here from pp.ml *)

(* Morally the parser gets a string and an edit_id, and gives back an AST.
 * Feedbacks during the parsing phase are attached to this edit_id.
 * The interpreter assignes an exec_id to the ast, and feedbacks happening
 * during interpretation are attached to the exec_id.
 * Only one among state_id and edit_id can be provided. *)

(** A [logger] takes a level plus a pretty printing doc and logs it *)
type logger = level -> Pp.std_ppcmds -> unit

(** [set_logger l] makes the [msg_*] to use [l] for logging *)
val set_logger : logger -> unit

(** [std_logger] standard logger to [stdout/stderr]  *)
val std_logger : logger

val color_terminal_logger : logger
(* This logger will apply the proper {!Pp_style} tags, and in
   particular use the formatters {!Pp_control.std_ft} and
   {!Pp_control.err_ft} to display those messages. Be careful this is
   not compatible with the Emacs mode!  *)

(** [feedback_logger] will produce feedback messages instead IO events *)
val feedback_logger : logger
val emacs_logger    : logger


(** [set_feeder] A feeder processes the feedback, [ignore] by default *)
val set_feeder : (feedback -> unit) -> unit

(** [feedback ?id ?route fb] produces feedback fb, with [route] and
    [id] set appropiatedly, if absent, it will use the defaults set by
    [set_id_for_feedback] *)
val feedback :
  ?id:edit_or_state_id -> ?route:route_id -> feedback_content -> unit

(** [set_id_for_feedback route id] Set the defaults for feedback *)
val set_id_for_feedback : ?route:route_id -> edit_or_state_id -> unit

(** [with_output_to_file file f x] executes [f x] with logging
    redirected to a file [file] *)
val with_output_to_file : string -> ('a -> 'b) -> 'a -> 'b

(** {6 output functions}

[msg_notice] do not put any decoration on output by default. If
possible don't mix it with goal output (prefer msg_info or
msg_warning) so that interfaces can dispatch outputs easily. Once all
interfaces use the xml-like protocol this constraint can be
relaxed. *)
(* Should we advertise these functions more? Should they be the ONLY
   allowed way to output something? *)

val msg_info : Pp.std_ppcmds -> unit
(** Message that displays information, usually in verbose mode, such as [Foobar
    is defined] *)

val msg_notice : Pp.std_ppcmds -> unit
(** Message that should be displayed, such as [Print Foo] or [Show Bar]. *)

val msg_warning : Pp.std_ppcmds -> unit
(** Message indicating that something went wrong, but without serious
    consequences. *)

val msg_error : Pp.std_ppcmds -> unit
(** Message indicating that something went really wrong, though still
    recoverable; otherwise an exception would have been raised. *)

val msg_debug : Pp.std_ppcmds -> unit
(** For debugging purposes *)




