open Names

(*
  [build_inductive parametrize funnames funargs returned_types bodies]
  constructs and saves the graphs of the functions [funnames] taking [funargs] as arguments
  and returning [returned_types] using bodies [bodies]
*)

val build_inductive :
(*  (ModPath.t * DirPath.t) option ->
  Id.t list -> (* The list of function name *) 
 *)
  Evd.evar_map ->
  Constr.pconstant list -> 
  (Name.t*Glob_term.glob_constr*Glob_term.glob_constr option) list list -> (* The list of function args *)
  Constrexpr.constr_expr list -> (* The list of function returned type *)
  Glob_term.glob_constr list -> (* the list of body *)
  unit

