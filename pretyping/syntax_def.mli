
(* $Id$ *)

(*i*)
open Names
open Rawterm
(*i*)

(* Syntactic definitions. *)

val declare_syntactic_definition : identifier -> rawconstr -> unit

val search_syntactic_definition : section_path -> rawconstr

val locate_syntactic_definition : section_path -> section_path


