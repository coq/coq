open Ascent;;

val xlate_vernac : Coqast.t -> ct_COMMAND;;
val xlate_tactic : Coqast.t -> ct_TACTIC_COM;;
val xlate_formula : Coqast.t -> ct_FORMULA;;
val xlate_int : Coqast.t -> ct_INT;;
val xlate_string : Coqast.t -> ct_STRING;;
val xlate_id : Coqast.t -> ct_ID;;
val xlate_vernac_list : Coqast.t -> ct_COMMAND_LIST;;

val g_nat_syntax_flag : bool ref;;
val set_flags : (unit -> unit) ref;;
val set_xlate_mut_stuff : (Coqast.t -> Coqast.t) -> unit;;
val declare_in_coq : (unit -> unit);;
