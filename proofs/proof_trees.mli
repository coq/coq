(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Stamps
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
val status_of_proof   : proof_tree -> pf_status
val is_complete_proof : proof_tree -> bool
val is_leaf_proof     : proof_tree -> bool
val is_tactic_proof   : proof_tree -> bool


(*s A global constraint is a mappings of existential variables with
    some extra information for the program and mimick tactics. *)

type global_constraints = enamed_declarations timestamped

(*s A readable constraint is a global constraint plus a focus set
    of existential variables and a signature. *)

type evar_recordty = {
  hyps  : named_context;
  decls : enamed_declarations }

and readable_constraints = evar_recordty timestamped

val rc_of_gc  : global_constraints -> goal -> readable_constraints
val rc_add    : readable_constraints -> int * goal -> readable_constraints
val get_hyps  : readable_constraints -> named_context
val get_env   : readable_constraints -> env
val get_decls : readable_constraints -> enamed_declarations
val get_gc    : readable_constraints -> global_constraints
val remap     : readable_constraints -> int * goal -> readable_constraints

val pf_lookup_name_as_renamed : 
  named_context -> constr -> identifier -> int option
val pf_lookup_index_as_renamed : constr -> int -> int option


(*s Pretty printing functions. *)

(*i*)
open Pp
(*i*)

val pr_goal      : goal -> std_ppcmds
val pr_subgoals  : goal list -> std_ppcmds
val pr_subgoal   : int -> goal list -> std_ppcmds

val pr_decl      : goal -> std_ppcmds
val pr_decls     : global_constraints -> std_ppcmds
val pr_evc       : readable_constraints -> std_ppcmds

val prgl         : goal -> std_ppcmds
val pr_seq       : goal -> std_ppcmds
val pr_evars     : (int * goal) list -> std_ppcmds
val pr_evars_int : int -> (int * goal) list -> std_ppcmds
val pr_subgoals_existential : enamed_declarations -> goal list -> std_ppcmds

(* Gives the ast corresponding to a tactic argument *)
val ast_of_cvt_arg : tactic_arg ->  Coqast.t 
