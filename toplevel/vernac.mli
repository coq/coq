(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)

(** Read a vernac command on the specified input (parse only).
   Raises [End_of_file] if EOF (or Ctrl-D) is reached. *)

val parse_sentence : Pcoq.Gram.parsable * in_channel option ->
 Loc.t * Vernacexpr.vernac_expr

(** Reads and executes vernac commands from a stream.
   The boolean [just_parsing] disables interpretation of commands. *)

exception End_of_input

val just_parsing : bool ref

val eval_expr : Loc.t * Vernacexpr.vernac_expr -> unit

(** Load a vernac file, verbosely or not. Errors are annotated with file
   and location *)

val load_vernac : bool -> string -> unit


(** Compile a vernac file, verbosely or not (f is assumed without .v suffix) *)

val compile : bool -> string -> unit

val is_navigation_vernac : Vernacexpr.vernac_expr -> bool

(** Has an exception been annotated with some file locations ? *)

type location_files = { outer : string; inner : string }

val get_exn_files : Exninfo.info -> location_files option
