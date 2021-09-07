(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  glob_constr_ltac_closure -> Environ.env -> evar_map -> evar_map
