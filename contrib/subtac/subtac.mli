val require_library : string -> unit
val subtac_one_fixpoint :
  'a ->
  'b ->
  (Names.identifier * (int * Topconstr.recursion_order_expr) *
   Topconstr.local_binder list * Topconstr.constr_expr *
   Topconstr.constr_expr) *
  'c ->
  (Names.identifier * (int * Topconstr.recursion_order_expr) *
   Topconstr.local_binder list * Topconstr.constr_expr *
   Topconstr.constr_expr) *
  'c
val subtac_fixpoint : 'a -> 'b -> unit
val subtac : Util.loc * Vernacexpr.vernac_expr -> unit
