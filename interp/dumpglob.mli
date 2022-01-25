(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val start_dump_glob : vfile:string -> vofile:string -> unit
val end_dump_glob : unit -> unit

val dump : unit -> bool

type glob_output =
  | NoGlob
  | Feedback
  | MultFiles                   (* one glob file per .v file *)
  | File of string              (* Single file for all coqc arguments *)

(** [push_output o] temporarily overrides the output location to [o].
    The original output can be restored using [pop_output] *)
val push_output : glob_output -> unit

(** Restores the original output that was overridden by [push_output] *)
val pop_output : unit -> unit

(** Alias for [push_output NoGlob] *)
val pause : unit -> unit

(** Deprecated alias for [pop_output] *)
val continue : unit -> unit
[@@ocaml.deprecated "Use pop_output"]

val with_glob_output : glob_output -> (unit -> 'a) -> unit -> 'a

val add_glob : ?loc:Loc.t -> Names.GlobRef.t -> unit
val add_glob_kn : ?loc:Loc.t -> Names.KerName.t -> unit

val dump_definition : Names.lident -> bool -> string -> unit
val dump_moddef : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_modref  : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_reference  : ?loc:Loc.t -> string -> string -> string -> unit
val dump_secvar : ?loc:Loc.t -> Names.Id.t -> unit
val dump_libref : ?loc:Loc.t -> Names.DirPath.t -> string -> unit
val dump_notation_location : (int * int) list -> Constrexpr.notation ->
  (Notation.notation_location * Notation_term.scope_name option) -> unit
val dump_binding : ?loc:Loc.t -> string -> unit
val dump_notation :
  Constrexpr.notation CAst.t ->
  Notation_term.scope_name option -> bool -> unit

val dump_constraint : Names.lname -> bool -> string -> unit

val dump_string : string -> unit

val type_of_global_ref : Names.GlobRef.t -> string

(** Registration of constant information *)
val add_constant_kind : Names.Constant.t -> Decls.logical_kind -> unit
val constant_kind : Names.Constant.t -> Decls.logical_kind
