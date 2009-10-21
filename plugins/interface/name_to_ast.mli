val name_to_ast : Libnames.reference -> Vernacexpr.vernac_expr;;
val inductive_to_ast_list : Names.mutual_inductive -> Vernacexpr.vernac_expr list;;
val constant_to_ast_list : Names.constant -> Vernacexpr.vernac_expr list;;
val variable_to_ast_list : Names.variable -> Vernacexpr.vernac_expr list;;
val leaf_entry_to_ast_list : (Libnames.full_path * Names.kernel_name) * Libobject.obj -> Vernacexpr.vernac_expr list;;
