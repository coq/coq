
(*i $Id$ i*)

(*i*)
open Names
open Term
open Tacmach
(*i*)

val half_inv_tac : identifier -> tactic
val inv_tac : identifier -> tactic
val inv_clear_tac : identifier -> tactic
val half_dinv_tac : identifier -> tactic
val dinv_tac : identifier -> tactic
val dinv_clear_tac : identifier -> tactic
val half_dinv_with : identifier -> constr -> tactic
val dinv_with : identifier -> constr -> tactic
val dinv_clear_with : identifier -> constr -> tactic

val invIn_tac : string -> identifier -> identifier list -> tactic
