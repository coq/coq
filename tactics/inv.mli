
(* $Id$ *)

(*i*)
open Names
open Tacmach
(*i*)

val inv_tac : identifier -> tactic
val inv_clear_tac : identifier -> tactic
val half_dinv_tac : identifier -> tactic
val dinv_tac : identifier -> tactic
val dinv_clear_tac : identifier -> tactic
val half_dinv_with : identifier -> Coqast.t -> tactic
val dinv_with : identifier -> Coqast.t -> tactic
val dinv_clear_with : identifier -> Coqast.t -> tactic
val invIn_tac : string -> identifier -> identifier list -> tactic
