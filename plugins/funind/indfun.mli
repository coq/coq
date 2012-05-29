open Errors
open Util
open Names
open Term
open Pp
open Indfun_common
open Libnames
open Glob_term
open Declarations
open Misctypes

val do_generate_principle :  
  bool -> 
  (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list -> 
  unit


val functional_induction :  
  bool ->
  Term.constr ->
  (Term.constr * Term.constr bindings) option ->
  intro_pattern_expr Pp.located option ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma


val make_graph :  Libnames.global_reference -> unit
