open Names
open Tactypes

val warn_cannot_define_graph : ?loc:Loc.t -> Pp.t * Pp.t -> unit

val warn_cannot_define_principle : ?loc:Loc.t -> Pp.t * Pp.t -> unit

val do_generate_principle :  
  bool -> 
  (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list -> 
  unit


val functional_induction :  
  bool ->
  EConstr.constr ->
  (EConstr.constr * EConstr.constr bindings) option ->
  Ltac_plugin.Tacexpr.or_and_intro_pattern option ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma


val make_graph : GlobRef.t -> unit
