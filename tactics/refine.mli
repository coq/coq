
(*i $Id$ i*)

open Term
open Tacmach

val refine : (int * constr) list * constr -> tactic
val refine_tac : (int * constr) list * constr -> tactic
