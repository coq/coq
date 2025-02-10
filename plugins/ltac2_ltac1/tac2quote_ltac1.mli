(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Ltac2_plugin.Tac2dyn

val wit_ltac1 : (Id.t CAst.t list * Ltac_plugin.Tacexpr.raw_tactic_expr, Id.t list * Ltac_plugin.Tacexpr.glob_tactic_expr) Arg.tag
(** Ltac1 AST quotation, seen as a 'tactic'. Its type is unit in Ltac2. *)

val wit_ltac1val : (Id.t CAst.t list * Ltac_plugin.Tacexpr.raw_tactic_expr, Id.t list * Ltac_plugin.Tacexpr.glob_tactic_expr) Arg.tag
(** Ltac1 AST quotation, seen as a value-returning expression, with type Ltac1.t. *)

val ltac1 : Geninterp.Val.t Ltac2_plugin.Tac2ffi.repr
