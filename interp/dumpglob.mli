(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)


val open_glob_file : string -> unit
val close_glob_file : unit -> unit

val dump : unit -> bool
val multi_dump : unit -> bool

val noglob : unit -> unit
val dump_to_stdout : unit -> unit
val dump_into_file : string -> unit
val dump_to_dotglob : unit -> unit

val pause : unit -> unit
val continue : unit -> unit

type coqdoc_state = Lexer.location_table
val coqdoc_freeze : unit -> coqdoc_state
val coqdoc_unfreeze : coqdoc_state -> unit

val add_glob : Util.loc -> Libnames.global_reference -> unit
val add_glob_kn : Util.loc -> Names.kernel_name -> unit

val dump_definition : Util.loc * Names.identifier -> bool -> string -> unit
val dump_moddef : Util.loc -> Names.module_path -> string -> unit
val dump_modref  : Util.loc -> Names.module_path -> string -> unit
val dump_reference  : Util.loc -> string -> string -> string -> unit
val dump_libref : Util.loc -> Names.dir_path -> string -> unit
val dump_notation_location : (int * int) list -> Topconstr.notation -> (Notation.notation_location * Topconstr.scope_name option) -> unit
val dump_binding : Util.loc -> Names.Idset.elt -> unit
val dump_notation : Util.loc * (Topconstr.notation * Notation.notation_location) -> Topconstr.scope_name option -> bool -> unit
val dump_constraint :  Topconstr.typeclass_constraint -> bool -> string -> unit
val dump_local_binder : Topconstr.local_binder -> bool -> string -> unit

val dump_string : string -> unit

