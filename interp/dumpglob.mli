(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val open_glob_file : string -> unit
val close_glob_file : unit -> unit

val start_dump_glob : string -> unit
val end_dump_glob : unit -> unit

val dump : unit -> bool

val noglob : unit -> unit
val dump_into_file : string -> unit (** special handling of "stdout" *)
val dump_to_dotglob : unit -> unit
val feedback_glob : unit -> unit

val pause : unit -> unit
val continue : unit -> unit

val add_glob : Loc.t -> Globnames.global_reference -> unit
val add_glob_kn : Loc.t -> Names.kernel_name -> unit

val dump_definition : Loc.t * Names.Id.t -> bool -> string -> unit
val dump_moddef : Loc.t -> Names.module_path -> string -> unit
val dump_modref  : Loc.t -> Names.module_path -> string -> unit
val dump_reference  : Loc.t -> string -> string -> string -> unit
val dump_libref : Loc.t -> Names.DirPath.t -> string -> unit
val dump_notation_location : (int * int) list -> Constrexpr.notation ->
  (Notation.notation_location * Notation_term.scope_name option) -> unit
val dump_binding : Loc.t -> Names.Id.Set.elt -> unit
val dump_notation :
  Loc.t * (Constrexpr.notation * Notation.notation_location) ->
  Notation_term.scope_name option -> bool -> unit
val dump_constraint :
  Constrexpr.typeclass_constraint -> bool -> string -> unit

val dump_string : string -> unit

val type_of_global_ref : Globnames.global_reference -> string 
