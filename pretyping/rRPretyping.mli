(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ
open Evd
open Glob_term
open Rewrite_rules_ops

val eval_pretyper_pattern : env -> evar_map -> glob_constr -> names * (int Evar.Map.t * UVars.sort_level_subst) * Evd.evar_map * Univ.UnivConstraints.t Sorts.QVar.Map.t * pattern * unsafe_judgment
