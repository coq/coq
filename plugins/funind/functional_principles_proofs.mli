open Names
open Term

val prove_princ_for_struct :
  Evd.evar_map ref ->
  bool ->
  int -> constant array -> constr array -> int -> Tacmach.tactic


val prove_principle_for_gen :
  constant*constant*constant -> (* name of the function, the functional and the fixpoint equation *)
  Indfun_common.tcc_lemma_value ref -> (* a pointer to the obligation proofs lemma *)
  bool -> (* is that function uses measure *)
  int -> (* the number of recursive argument *)
  types -> (* the type of the recursive argument *)
  constr -> (* the wf relation used to prove the function *)
  Tacmach.tactic


(* val is_pte  : rel_declaration -> bool  *)
