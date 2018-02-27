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

(* Legacy-style logging messages (used to be in Pp) *)
type level =
  | Debug
  | Info
  | Notice
  | Warning
  | Error


(** Document unique identifier for serialization *)
type doc_id = int

(** Coq "semantic" infos obtained during execution *)
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
  | Custom of Loc.t option * string * xml
  (* Generic messages *)
  | Message of level * Loc.t option * Pp.t

type feedback = {
  doc_id   : doc_id;            (* The document being concerned *)
  span_id  : Stateid.t;         (* The document part concerned *)
  route    : route_id;          (* Extra routing info *)
  contents : feedback_content;  (* The payload *)
}

(** {6 Feedback sent, even asynchronously, to the user interface} *)

(* The interpreter assignes an state_id to the ast, and feedbacks happening
 * during interpretation are attached to it.
 *)

(** [add_feeder f] adds a feeder listiner [f], returning its id *)
val add_feeder : (feedback -> unit) -> int

(** [del_feeder fid] removes the feeder with id [fid] *)
val del_feeder : int -> unit

(** [feedback ?did ?sid ?route fb] produces feedback [fb], with
    [route] and [did, sid] set appropiatedly, if absent, it will use
    the defaults set by [set_id_for_feedback] *)
val feedback : ?did:doc_id -> ?id:Stateid.t -> ?route:route_id -> feedback_content -> unit

(** [set_id_for_feedback route id] Set the defaults for feedback *)
val set_id_for_feedback : ?route:route_id -> doc_id -> Stateid.t -> unit

(** {6 output functions}

[msg_notice] do not put any decoration on output by default. If
possible don't mix it with goal output (prefer msg_info or
msg_warning) so that interfaces can dispatch outputs easily. Once all
interfaces use the xml-like protocol this constraint can be
relaxed. *)
(* Should we advertise these functions more? Should they be the ONLY
   allowed way to output something? *)

val msg_info : ?loc:Loc.t -> Pp.t -> unit
(** Message that displays information, usually in verbose mode, such as [Foobar
    is defined] *)

val msg_notice : ?loc:Loc.t -> Pp.t -> unit
(** Message that should be displayed, such as [Print Foo] or [Show Bar]. *)

val msg_warning : ?loc:Loc.t -> Pp.t -> unit
(** Message indicating that something went wrong, but without serious
    consequences. *)

val msg_error : ?loc:Loc.t -> Pp.t -> unit
[@@ocaml.deprecated "msg_error is an internal function and should not be \
                     used unless you know what you are doing. Use \
                     [CErrors.user_err] instead."]

val msg_debug : ?loc:Loc.t -> Pp.t -> unit
(** For debugging purposes *)

val console_feedback_listener : Format.formatter -> feedback -> unit
(** Helper for tools willing to print to the feedback system *)

val warn_no_listeners : bool ref
(** The library will print a warning to the console if no listener is
    available by default; ML-clients willing to use Coq without a
    feedback handler should set this to false. *)
