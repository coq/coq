open Util
open Names
open Term
open Rawterm
open Proof_type
open Topconstr

val lemInv_gen : quantified_hypothesis -> constr -> tactic
val lemInvIn_gen : quantified_hypothesis -> constr -> identifier list -> tactic

val lemInv_clause : 
  quantified_hypothesis -> constr -> identifier list -> tactic

val inversion_lemma_from_goal :
  int -> identifier -> identifier located -> sorts -> bool ->
    (identifier -> tactic) -> unit
val add_inversion_lemma_exn :
  identifier -> constr_expr -> rawsort -> bool -> (identifier -> tactic) ->
    unit
