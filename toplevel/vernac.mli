
(*i $Id$ i*)

(* Parsing of vernacular. *)

(* Like [Exc_located], but specifies the outermost file read, the input buffer
   associated to the location of the error, and the error itself. *)

exception Error_in_file of string * (string * Coqast.loc) * exn

(* Read a vernac command on the specified input (parse only).
   Raises [End_of_file] if EOF (or Ctrl-D) is reached. *)

val parse_phrase : Pcoq.Gram.parsable * in_channel option -> Coqast.t

(* Reads and executes vernac commands from a stream.
   The boolean [just_parsing] disables interpretation of commands. *)

exception DuringCommandInterp of Coqast.loc * exn
exception End_of_input

val just_parsing : bool ref
val raw_do_vernac : Pcoq.Gram.parsable -> unit

(* Load a vernac file, verbosely or not. Errors are annotated with file
   and location *)

val load_vernac : bool -> string -> unit
