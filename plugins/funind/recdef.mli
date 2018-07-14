open Constr

val tclUSER_if_not_mes : 
  Tacmach.tactic ->
  bool -> 
  Names.Id.t list option -> 
  Tacmach.tactic
val recursive_definition :  
bool ->
           Names.Id.t ->
           Constrintern.internalization_env ->
           Constrexpr.constr_expr ->
           Constrexpr.constr_expr ->
           int -> Constrexpr.constr_expr -> (pconstant ->
            Indfun_common.tcc_lemma_value ref ->
            pconstant ->
            pconstant -> int -> EConstr.types -> int -> EConstr.constr -> unit) -> Constrexpr.constr_expr list -> unit


