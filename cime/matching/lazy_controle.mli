exception No_solution
exception Not_appliable

type 'pb disjunction = 'pb Lazy_list.llist

(*
and 'pb_disj rule_result = 
    Sol of 'pb_disj 
  | No_sol 
  | No_app
*)

val repeat : ('pb -> 'pb disjunction) -> 'pb -> 'pb disjunction
