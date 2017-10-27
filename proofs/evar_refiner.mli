(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Evd
open Glob_term
open Ltac_pretype

(** Refinement of existential variables. *)

type glob_constr_ltac_closure = ltac_var_map * glob_constr

val w_refine : evar * evar_info ->
  glob_constr_ltac_closure -> evar_map -> evar_map
