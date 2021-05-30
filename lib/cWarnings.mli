(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type status = Disabled | Enabled | AsError

val create : name:string -> category:string -> ?default:status ->
             ('a -> Pp.t) -> ?loc:Loc.t -> 'a -> unit

val get_flags : unit -> string
val set_flags : string -> unit

(** Cleans up a user provided warnings status string, e.g. removing unknown
    warnings (in which case a warning is emitted) or subsumed warnings . *)
val normalize_flags_string : string -> string

(** [with_warn "-xxx,+yyy..." f x] calls [f x] after setting the
   warnings as specified in the string (keeping other previously set
   warnings), and restores current warnings after [f()] returns or
   raises an exception. If both f and restoring the warnings raise
   exceptions, the latter is raised. *)
val with_warn: string -> ('b -> 'a) -> 'b -> 'a
