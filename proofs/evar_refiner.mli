(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd
open Glob_term
open Ltac_pretype

(** Refinement of existential variables. *)

type glob_constr_ltac_closure = ltac_var_map * glob_constr

val w_refine : Evar.t * evar_info ->
  glob_constr_ltac_closure -> evar_map -> evar_map
