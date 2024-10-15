(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Weak-head cbn reduction. Despite the name, the cbn reduction is a complex
    reduction distinct from call-by-name or call-by-need. *)
val whd_cbn :
  RedFlags.reds ->
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr

(** Strong variant of cbn reduction. *)
val norm_cbn :
  RedFlags.reds ->
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr
