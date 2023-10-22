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

val maybe_stop : environment -> Loc.t option -> bool

val push_locs : Loc.t option -> environment -> Loc.t option list

val push_stack : string * Loc.t option -> environment ->
                 (string * Loc.t option) list option

val read_loop : unit -> unit

val fmt_stack2 : (string * Loc.t option) list option -> unit ->
                string list

val fmt_vars2 : varmap list -> int -> DebuggerTypes.db_vars_rty

val dump_Cexpr : Loc.t option -> Tac2expr.raw_tacexpr -> unit

val dump_Gexpr : ?indent:int -> ?p:string -> Tac2expr.glb_tacexpr -> unit
