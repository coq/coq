(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

(** Coq "semantic" infos obtained during parsing/execution *)
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

type feedback = {
  id : edit_or_state_id;
  content : feedback_content;
}

val of_feedback : feedback -> xml
val to_feedback : xml -> feedback
val is_feedback : xml -> bool

