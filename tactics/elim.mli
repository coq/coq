(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Proof_type
open Tacmach
open Tacticals
(*i*)

(* Eliminations tactics. *)

val introElimAssumsThen :
  (branch_assumptions -> tactic) -> branch_args -> tactic

val introCaseAssumsThen :
  (branch_assumptions -> tactic) -> branch_args -> tactic

val general_decompose : (identifier * constr -> bool) -> constr -> tactic
val decompose_nonrec  : constr -> tactic
val decompose_and     : constr -> tactic
val decompose_or      : constr -> tactic
val h_decompose       : inductive list -> constr -> tactic
val h_decompose_or    : constr -> tactic
val h_decompose_and   : constr -> tactic

val double_ind : Rawterm.quantified_hypothesis -> Rawterm.quantified_hypothesis -> tactic
val h_double_induction : Rawterm.quantified_hypothesis -> Rawterm.quantified_hypothesis->tactic

val intro_pattern     : Tacexpr.intro_pattern_expr      -> tactic
val intros_pattern    : Tacexpr.intro_pattern_expr list -> tactic
(*
val dyn_intro_pattern : tactic_arg list    -> tactic
val v_intro_pattern   : tactic_arg list    -> tactic
*)
val h_intro_patterns  : Tacexpr.intro_pattern_expr list -> tactic
