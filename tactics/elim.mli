(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Proof_type
open Tacmach
open Genarg
open Tacticals

(** Eliminations tactics. *)

val introElimAssumsThen :
  (branch_assumptions -> tactic) -> branch_args -> tactic

val introCaseAssumsThen :
  (intro_pattern_expr Util.located list -> branch_assumptions -> tactic) ->
    branch_args -> tactic

val general_decompose : (identifier * constr -> bool) -> constr -> tactic
val decompose_nonrec  : constr -> tactic
val decompose_and     : constr -> tactic
val decompose_or      : constr -> tactic
val h_decompose       : inductive list -> constr -> tactic
val h_decompose_or    : constr -> tactic
val h_decompose_and   : constr -> tactic

val double_ind : Rawterm.quantified_hypothesis -> Rawterm.quantified_hypothesis -> tactic
val h_double_induction : Rawterm.quantified_hypothesis -> Rawterm.quantified_hypothesis->tactic
