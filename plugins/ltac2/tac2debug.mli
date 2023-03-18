(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type environment = Tac2env.environment

type varmap = Tac2ffi.valexpr Names.Id.Map.t

val stop_stuff : environment -> Loc.t option -> bool

val push_locs : Loc.t option -> environment -> Loc.t option list

val push_stack : string * Loc.t option -> environment ->
                 (string * Loc.t option) list option

val read_loop : unit -> unit

val fmt_stack2 : (string * Loc.t option) list option -> unit ->
                string list

val fmt_vars2 : varmap list -> int -> DebugHook.Answer.vars

val dump_expr2 : ?indent:int -> ?p:string -> Tac2expr.glb_tacexpr -> unit
