(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ

(***********************************************************************
  s Call-by-value reduction *)

(** Entry point for cbv normalization of a constr *)
type cbv_infos

val create_cbv_infos : RedFlags.reds -> strong:bool -> env -> Evd.evar_map -> cbv_infos
val cbv_norm         : cbv_infos -> constr -> constr
