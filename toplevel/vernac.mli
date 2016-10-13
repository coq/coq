(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)

(** Read a vernac command on the specified input (parse only).
   Raises [End_of_file] if EOF (or Ctrl-D) is reached. *)

val parse_sentence : Pcoq.Gram.coq_parsable * in_channel option ->
 Loc.t * Vernacexpr.vernac_expr

(** Reads and executes vernac commands from a stream. *)

exception End_of_input

val process_expr : Pcoq.Gram.coq_parsable -> Loc.t * Vernacexpr.vernac_expr -> unit

(** Set XML hooks *)
val xml_start_library : (unit -> unit) Hook.t
val xml_end_library   : (unit -> unit) Hook.t

(** Load a vernac file, verbosely or not. Errors are annotated with file
   and location *)

val load_vernac : bool -> string -> unit


(** Compile a vernac file, verbosely or not (f is assumed without .v suffix) *)

val compile : bool -> string -> unit

val is_navigation_vernac : Vernacexpr.vernac_expr -> bool
