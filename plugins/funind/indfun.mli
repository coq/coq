open Misctypes

val do_generate_principle :  
  bool -> 
  (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list -> 
  unit


val functional_induction :  
  bool ->
  Term.constr ->
  (Term.constr * Term.constr bindings) option ->
  Tacexpr.or_and_intro_pattern option ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma


val make_graph :  Globnames.global_reference -> unit
