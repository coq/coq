(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val open_glob_file : string -> unit
val close_glob_file : unit -> unit

val start_dump_glob : vfile:string -> vofile:string -> unit
val end_dump_glob : unit -> unit

val dump : unit -> bool

val noglob : unit -> unit
val dump_into_file : string -> unit (** special handling of "stdout" *)
val dump_to_dotglob : unit -> unit
val feedback_glob : unit -> unit

val pause : unit -> unit
val continue : unit -> unit

val add_glob : ?loc:Loc.t -> Names.GlobRef.t -> unit
val add_glob_kn : ?loc:Loc.t -> Names.KerName.t -> unit

val dump_definition : Names.lident -> bool -> string -> unit
val dump_moddef : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_modref  : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_reference  : ?loc:Loc.t -> string -> string -> string -> unit
val dump_libref : ?loc:Loc.t -> Names.DirPath.t -> string -> unit
val dump_notation_location : (int * int) list -> Constrexpr.notation ->
  (Notation.notation_location * Notation_term.scope_name option) -> unit
val dump_binding : ?loc:Loc.t -> Names.Id.Set.elt -> unit
val dump_notation :
  (Constrexpr.notation * Notation.notation_location) Loc.located ->
  Notation_term.scope_name option -> bool -> unit

val dump_constraint : Names.lname -> bool -> string -> unit

val dump_string : string -> unit

val type_of_global_ref : Names.GlobRef.t -> string
