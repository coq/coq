
open Names
open Term
open Rawterm
open Proof_type

val lemInv_gen : quantified_hypothesis -> constr -> tactic
val lemInvIn_gen : quantified_hypothesis -> constr -> identifier list -> tactic

val inversion_lemma_from_goal :
  int -> identifier -> identifier -> sorts -> bool ->
    (identifier -> tactic) -> unit
val add_inversion_lemma_exn :
  identifier -> Coqast.t -> Coqast.t -> bool -> (identifier -> tactic) -> unit

