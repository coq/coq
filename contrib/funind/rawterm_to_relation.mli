
(* val new_build_entry_lc :  *)
(*   Names.identifier list ->  *)
(*   (Names.name*Rawterm.rawconstr) list list ->  *)
(*   Topconstr.constr_expr list ->  *)
(*   Rawterm.rawconstr list ->  *)
(*   unit  *)

val build_inductive :
  bool -> 
  Names.identifier list ->
  (Names.name*Rawterm.rawconstr) list list ->
  Topconstr.constr_expr list ->
  Rawterm.rawconstr list ->
  unit

