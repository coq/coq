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

val mk_goal : named_context -> constr -> goal

val rule_of_proof     : proof_tree -> rule
val ref_of_proof      : proof_tree -> (rule * proof_tree list)
val children_of_proof : proof_tree -> proof_tree list
val goal_of_proof     : proof_tree -> goal
val subproof_of_proof : proof_tree -> proof_tree
val status_of_proof   : proof_tree -> int
val is_complete_proof : proof_tree -> bool
val is_leaf_proof     : proof_tree -> bool
val is_tactic_proof   : proof_tree -> bool

(*s A readable constraint is a global constraint plus a focus set
    of existential variables and a signature. *)

val rc_of_gc  : evar_map -> goal -> named_context sigma
val rc_add    : named_context sigma -> existential_key * goal -> 
  named_context sigma
val get_hyps  : named_context sigma -> named_context
val get_env   : named_context sigma -> env
val get_gc    : named_context sigma -> evar_map

val pf_lookup_name_as_renamed  : env -> constr -> identifier -> int option
val pf_lookup_index_as_renamed : env -> constr -> int -> int option


(*s Pretty printing functions. *)

(*i*)
open Pp
(*i*)

val pr_goal      : goal -> std_ppcmds
val pr_subgoals  : goal list -> std_ppcmds
val pr_subgoal   : int -> goal list -> std_ppcmds

val pr_decl      : goal -> std_ppcmds
val pr_decls     : evar_map -> std_ppcmds
val pr_evc       : named_context sigma -> std_ppcmds

val prgl         : goal -> std_ppcmds
val pr_seq       : goal -> std_ppcmds
val pr_evars     : (existential_key * goal) list -> std_ppcmds
val pr_evars_int : int -> (existential_key * goal) list -> std_ppcmds
val pr_subgoals_existential : evar_map -> goal list -> std_ppcmds
