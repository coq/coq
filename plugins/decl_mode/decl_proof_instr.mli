(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Refiner
open Names
open Term
open Tacmach
open Decl_mode

val go_to_proof_mode: unit -> unit
val return_from_tactic_mode: unit -> unit

val register_automation_tac: tactic -> unit

val automation_tac : tactic

val concl_refiner:
  Termops.meta_type_map -> constr -> Proof_type.goal sigma -> constr

val do_instr: Decl_expr.raw_proof_instr -> Proof.proof -> unit
val proof_instr: Decl_expr.raw_proof_instr -> unit

val tcl_change_info : Decl_mode.pm_info -> tactic

val execute_cases :
    Names.name ->
    Decl_mode.per_info ->
    (Term.constr -> Proof_type.tactic) ->
    (Names.Id.Set.elt * (Term.constr option * Term.constr list) list) list ->
    Term.constr list -> int -> Decl_mode.split_tree -> Proof_type.tactic

val tree_of_pats : 
  Id.t * (int * int) -> (Glob_term.cases_pattern*recpath) list list ->
  split_tree

val add_branch : 
  Id.t * (int * int) -> (Glob_term.cases_pattern*recpath) list list ->
  split_tree -> split_tree

val append_branch :
  Id.t *(int * int) -> int -> (Glob_term.cases_pattern*recpath) list list ->
  (Names.Id.Set.t * Decl_mode.split_tree) option ->
  (Names.Id.Set.t * Decl_mode.split_tree) option

val append_tree :
  Id.t * (int * int) -> int -> (Glob_term.cases_pattern*recpath) list list ->
  split_tree -> split_tree

val build_dep_clause :   Term.types Decl_expr.statement list ->
    Decl_expr.proof_pattern ->
    Decl_mode.per_info ->
    (Term.types Decl_expr.statement, Term.types Decl_expr.or_thesis)
    Decl_expr.hyp list -> Proof_type.goal Tacmach.sigma -> Term.types

val register_dep_subcase :    
    Names.Id.t * (int * int) ->
    Environ.env ->
    Decl_mode.per_info ->
    Glob_term.cases_pattern -> Decl_mode.elim_kind -> Decl_mode.elim_kind

val thesis_for :     Term.constr ->
    Term.constr -> Decl_mode.per_info -> Environ.env -> Term.constr

val close_previous_case : Proof.proof -> unit

val pop_stacks :
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list ->
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list

val push_head :   Term.constr ->
  Names.Id.Set.t ->
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list ->
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list

val push_arg : Term.constr ->
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list ->
  (Names.Id.t *
     (Term.constr option * Term.constr list) list) list

val hrec_for:
    Names.Id.t ->
    Decl_mode.per_info -> Proof_type.goal Tacmach.sigma ->
    Names.Id.t -> Term.constr

val consider_match :
   bool ->
    (Names.Id.Set.elt*bool) list ->
    Names.Id.Set.elt list ->
    (Term.types Decl_expr.statement, Term.types) Decl_expr.hyp list ->
    Proof_type.tactic

val init_tree:
    Names.Id.Set.t ->
    Names.inductive ->
    int option * Declarations.wf_paths ->
    (int ->
     (int option * Declarations.recarg Rtree.t) array ->
     (Names.Id.Set.t * Decl_mode.split_tree) option) ->
    Decl_mode.split_tree
