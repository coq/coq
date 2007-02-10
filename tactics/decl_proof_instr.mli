(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Refiner
open Names
open Term
open Tacmach

val go_to_proof_mode: unit -> unit
val return_from_tactic_mode: unit -> unit

val register_automation_tac: tactic -> unit

val automation_tac : tactic

val daimon_subtree: pftreestate -> pftreestate

val do_instr: Decl_expr.raw_proof_instr -> pftreestate -> pftreestate
val proof_instr: Decl_expr.raw_proof_instr -> unit

val tcl_change_info : Decl_mode.pm_info -> tactic

val mark_proof_tree_as_done : Proof_type.proof_tree -> Proof_type.proof_tree

val mark_as_done : pftreestate -> pftreestate

val execute_cases : bool ->
    Names.name ->
    Decl_mode.per_info ->
    (Term.constr -> Proof_type.tactic) ->
    (Names.Idset.elt * (Term.constr option * bool * Term.constr list) list) 
      list ->
    Decl_mode.split_tree -> Proof_type.tactic

val tree_of_pats :
    Environ.env ->
    Names.Idset.elt * int ->
    Rawterm.cases_pattern list list -> Decl_mode.split_tree
val add_branch :
    Environ.env ->
    Names.Idset.elt * int ->
    Rawterm.cases_pattern list list ->
    Decl_mode.split_tree -> Decl_mode.split_tree
val append_branch :
    Environ.env ->
    Names.Idset.elt * int ->
    int ->
    Rawterm.cases_pattern list list ->
    int ->
    (Names.Idset.t * Decl_mode.split_tree) option ->
    (Names.Idset.t * Decl_mode.split_tree) option

val append_tree :   Environ.env ->
    Names.Idset.elt * int ->
    int ->
    Rawterm.cases_pattern list list ->
    Decl_mode.split_tree -> Decl_mode.split_tree

val build_dep_clause :   Term.types Decl_expr.statement list ->
    Decl_expr.proof_pattern ->
    Decl_mode.per_info ->
    (Term.types Decl_expr.statement, Term.types Decl_expr.or_thesis)
    Decl_expr.hyp list -> Proof_type.goal Tacmach.sigma -> Term.types

val register_dep_subcase :    
    Names.identifier * int ->
    Environ.env ->
    Decl_mode.per_info ->
    Rawterm.cases_pattern -> Decl_mode.elim_kind -> Decl_mode.elim_kind

val thesis_for :     Term.constr ->
    Term.constr -> Decl_mode.per_info -> Environ.env -> Term.constr

val close_previous_case : pftreestate -> pftreestate

val test_fun : string -> unit


val pop_stacks :
  (Names.identifier * 
     (Term.constr option * bool * Term.constr list) list) list ->
  bool * 
    (Names.identifier * 
       (Term.constr option * bool * Term.constr list) list) list


val push_head :   Term.constr ->
  bool ->
  Names.Idset.t ->
  (Names.identifier * 
     (Term.constr option * bool * Term.constr list) list) list ->
  (Names.identifier * 
     (Term.constr option * bool * Term.constr list) list) list

val push_arg : Term.constr ->
  (Names.identifier * 
     (Term.constr option * bool * Term.constr list) list) list ->
  (Names.identifier * 
     (Term.constr option * bool * Term.constr list) list) list

val hrec_for: 
    Names.identifier ->
    Names.identifier ->
    Decl_mode.per_info -> Proof_type.goal Tacmach.sigma -> Term.constr option

val consider_match :
   bool ->
    (Names.Idset.elt*bool) list ->
    Names.Idset.elt list ->
    (Term.types Decl_expr.statement, Term.types) Decl_expr.hyp list ->
    Proof_type.tactic

val thus_tac : constr -> constr -> (metavariable * types) list ->
  tactic

val build_applist :    Term.types ->
    Term.metavariable list ->
    (Term.metavariable * Term.types) list * Term.types

