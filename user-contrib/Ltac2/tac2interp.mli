(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2expr
open Tac2ffi

type environment = Tac2env.environment

val empty_environment : environment

val interp : environment -> glb_tacexpr -> valexpr Proofview.tactic

(* val interp_app : closure -> ml_tactic *)

(** {5 Cross-boundary encodings} *)

val get_env : Ltac_pretype.unbound_ltac_var_map -> environment
val set_env : environment -> Ltac_pretype.unbound_ltac_var_map -> Ltac_pretype.unbound_ltac_var_map

(** {5 Exceptions} *)

exception LtacError of KerName.t * valexpr array
(** Ltac2-defined exceptions seen from OCaml side *)

(** {5 Backtrace} *)

val get_backtrace : backtrace Proofview.tactic

val with_frame : frame -> 'a Proofview.tactic -> 'a Proofview.tactic

val print_ltac2_backtrace : bool ref
