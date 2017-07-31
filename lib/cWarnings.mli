(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type status = Disabled | Enabled | AsError

val set_current_loc : Loc.t option -> unit

val create : name:string -> category:string -> ?default:status ->
             ('a -> Pp.t) -> ?loc:Loc.t -> 'a -> unit

val get_flags : unit -> string
val set_flags : string -> unit

(** Cleans up a user provided warnings status string, e.g. removing unknown
    warnings (in which case a warning is emitted) or subsumed warnings . *)
val normalize_flags_string : string -> string
