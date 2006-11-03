val mkAppExplC :
  Libnames.reference * Topconstr.constr_expr list -> Topconstr.constr_expr
val mkSubset :
  Names.name Util.located ->
  Topconstr.constr_expr -> Topconstr.constr_expr -> Topconstr.constr_expr
val mkProj1 :
  Topconstr.constr_expr ->
  Topconstr.constr_expr -> Topconstr.constr_expr -> Topconstr.constr_expr
val mkProj2 :
  Topconstr.constr_expr ->
  Topconstr.constr_expr -> Topconstr.constr_expr -> Topconstr.constr_expr
val list_of_local_binders :
  Topconstr.local_binder list ->
  (Names.name Util.located * Topconstr.constr_expr) list
val pr_binder_list :
  (('a * Names.name) * Topconstr.constr_expr) list -> Pp.std_ppcmds
val rewrite_rec_calls : 'a -> 'b -> 'b
