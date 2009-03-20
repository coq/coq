open Ascent;;

val xlate_vernac : Vernacexpr.vernac_expr -> ct_COMMAND;;
val xlate_tactic : Tacexpr.raw_tactic_expr -> ct_TACTIC_COM;;
val xlate_formula : Topconstr.constr_expr -> ct_FORMULA;;
val xlate_ident : Names.identifier -> ct_ID;;
val xlate_vernac_list : Vernacexpr.vernac_expr -> ct_COMMAND_LIST;;

