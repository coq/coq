open Names
open Term

val prove_princ_for_struct :
  bool ->
  int -> constant array -> constr array -> int -> Tacmach.tactic


val prove_principle_for_gen :
  constant*constant*constant -> (* name of the function, the fonctionnal and the fixpoint equation *)
  constr option ref -> (* a pointer to the obligation proofs lemma *)
  bool -> (* is that function uses measure *)
  int -> (* the number of recursive argument *)
  types -> (* the type of the recursive argument *)
  constr -> (* the wf relation used to prove the function *)
  Tacmach.tactic


(* val is_pte  : rel_declaration -> bool  *)
