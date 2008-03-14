


(*
  [build_inductive parametrize funnames funargs returned_types bodies] 
  constructs and saves the graphs of the functions [funnames] taking [funargs] as arguments 
  and returning [returned_types] using bodies [bodies]
*)

val build_inductive :
  Names.identifier list -> (* The list of function name *)
  (Names.name*Rawterm.rawconstr*bool) list list -> (* The list of function args *)
  Topconstr.constr_expr list -> (* The list of function returned type *)
  Rawterm.rawconstr list -> (* the list of body *)
  unit

