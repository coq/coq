open Ascent;;

val xlate_vernac : Vernacexpr.vernac_expr -> ct_COMMAND;;
val xlate_tactic : Tacexpr.raw_tactic_expr -> ct_TACTIC_COM;;
val xlate_formula : Ctast.t -> ct_FORMULA;;
val xlate_int : Ctast.t -> ct_INT;;
val xlate_string : Ctast.t -> ct_STRING;;
val xlate_ident : Names.identifier -> ct_ID;;
val xlate_vernac_list : Vernacexpr.vernac_expr -> ct_COMMAND_LIST;;

val g_nat_syntax_flag : bool ref;;
val set_flags : (unit -> unit) ref;;
val set_xlate_mut_stuff : (Ctast.t -> Ctast.t) -> unit;;
val declare_in_coq : (unit -> unit);;
