(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parsing of vernacular. *)

(** Read a vernac command on the specified input (parse only).
   Raises [End_of_file] if EOF (or Ctrl-D) is reached. *)

val parse_sentence : Pcoq.Gram.parsable * in_channel option ->
 Pp.loc * Vernacexpr.vernac_expr

(** Reads and executes vernac commands from a stream.
   The boolean [just_parsing] disables interpretation of commands. *)

exception DuringCommandInterp of Pp.loc * exn
exception End_of_input

val just_parsing : bool ref

(** [eval_expr] executes one vernacular command. By default the command is
   considered as non-state-preserving, in which case we add it to the
   Backtrack stack (triggering a save of a frozen state and the generation
   of a new state label). An example of state-preserving command is one coming
   from the query panel of Coqide. *)

val eval_expr : ?preserving:bool -> Pp.loc * Vernacexpr.vernac_expr -> unit
val raw_do_vernac : Pcoq.Gram.parsable -> unit

(** Set XML hooks *)
val set_xml_start_library : (unit -> unit) -> unit
val set_xml_end_library   : (unit -> unit) -> unit

(** Load a vernac file, verbosely or not. Errors are annotated with file
   and location *)

val load_vernac : bool -> string -> unit


(** Compile a vernac file, verbosely or not (f is assumed without .v suffix) *)

val compile : bool -> string -> unit
