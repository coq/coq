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
val h_decompose       : Libnames.section_path list -> constr -> tactic

val double_ind : int -> int -> tactic

val intro_pattern     : intro_pattern      -> tactic
val intros_pattern    : intro_pattern list -> tactic
val dyn_intro_pattern : tactic_arg list    -> tactic
val v_intro_pattern   : tactic_arg list    -> tactic
val h_intro_pattern   : intro_pattern      -> tactic
