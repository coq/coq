

(* val evaluable_of_global_reference : Libnames.global_reference -> Names.evaluable_global_reference *)
val tclUSER_if_not_mes : 
  Proof_type.tactic ->
  bool -> 
  Names.Id.t list option -> 
  Proof_type.tactic
val recursive_definition :  
bool ->
           Names.Id.t ->
           Constrintern.internalization_env ->
           Constrexpr.constr_expr ->
           Constrexpr.constr_expr ->
           int -> Constrexpr.constr_expr -> (Term.pconstant ->
            Indfun_common.tcc_lemma_value ref ->
            Term.pconstant ->
            Term.pconstant -> int -> Term.types -> int -> Term.constr -> 'a) -> Constrexpr.constr_expr list -> unit


