(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Environ
open Proof_type
(*i*)

(* This module declares readable constraints, and a few utilities on
   constraints and proof trees *)

val mk_goal : named_context_val -> constr -> Dyn.t option -> goal

val rule_of_proof     : proof_tree -> rule
val ref_of_proof      : proof_tree -> (rule * proof_tree list)
val children_of_proof : proof_tree -> proof_tree list
val goal_of_proof     : proof_tree -> goal
val subproof_of_proof : proof_tree -> proof_tree
val status_of_proof   : proof_tree -> int
val is_complete_proof : proof_tree -> bool
val is_leaf_proof     : proof_tree -> bool
val is_tactic_proof   : proof_tree -> bool

val pf_lookup_name_as_renamed  : env -> constr -> identifier -> int option
val pf_lookup_index_as_renamed : env -> constr -> int -> int option

val is_proof_instr : rule -> bool
val is_focussing_command : rule -> bool

(*s Pretty printing functions. *)

(*i*)
open Pp
(*i*)

val db_pr_goal : goal -> std_ppcmds
