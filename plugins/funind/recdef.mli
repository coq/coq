

(* val evaluable_of_global_reference : Libnames.global_reference -> Names.evaluable_global_reference *)
val tclUSER_if_not_mes : 
  Proof_type.tactic ->
  bool -> 
  Names.identifier list option -> 
  Proof_type.tactic
val recursive_definition :  
bool ->
           Names.identifier ->
           Constrintern.internalization_env ->
           Topconstr.constr_expr ->
           Topconstr.constr_expr ->
           int -> Topconstr.constr_expr -> (Names.constant ->
            Term.constr option ref ->
            Names.constant ->
            Names.constant -> int -> Term.types -> int -> Term.constr -> 'a) -> Topconstr.constr_expr list -> unit


