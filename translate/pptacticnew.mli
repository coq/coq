(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(* $Id$ *)

open Pp
open Genarg
open Tacexpr
open Proof_type
open Topconstr

val pr_raw_tactic : Environ.env -> raw_tactic_expr -> std_ppcmds
val pr_gen : Environ.env ->
  (constr_expr, raw_tactic_expr) generic_argument -> std_ppcmds
