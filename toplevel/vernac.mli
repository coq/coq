(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Parsing of vernacular. *)

(* Read a vernac command on the specified input (parse only).
   Raises [End_of_file] if EOF (or Ctrl-D) is reached. *)

val parse_phrase : Pcoq.Gram.parsable * in_channel option ->
  Util.loc * Vernacexpr.vernac_expr

(* Reads and executes vernac commands from a stream.
   The boolean [just_parsing] disables interpretation of commands. *)

exception DuringCommandInterp of Util.loc * exn
exception End_of_input

val just_parsing : bool ref
val raw_do_vernac : Pcoq.Gram.parsable -> unit

(* Set XML hooks *)
val set_xml_start_library : (unit -> unit) -> unit
val set_xml_end_library   : (unit -> unit) -> unit

(* Load a vernac file, verbosely or not. Errors are annotated with file
   and location *)

val load_vernac : bool -> string -> unit


(* Compile a vernac file, verbosely or not (f is assumed without .v suffix) *)

val compile : bool -> string -> unit

(* Interpret a vernac AST *)

val vernac_com :
  (Vernacexpr.vernac_expr -> unit) ->
  Util.loc * Vernacexpr.vernac_expr -> unit
