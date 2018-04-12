(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
