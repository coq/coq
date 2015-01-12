(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Evd
open Pretyping

(** Refinement of existential variables. *)

val w_refine : evar * evar_info ->
  glob_constr_ltac_closure -> evar_map -> evar_map

val instantiate_pf_com :
  Evd.evar -> Constrexpr.constr_expr -> Evd.evar_map -> Evd.evar_map

(** the instantiate tactic was moved to [tactics/evar_tactics.ml] *)
