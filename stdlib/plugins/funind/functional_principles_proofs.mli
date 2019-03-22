open Names

val prove_princ_for_struct :
  Evd.evar_map ref ->
  bool ->
  int -> Constant.t array -> EConstr.constr array -> int -> Tacmach.tactic


val prove_principle_for_gen :
  Constant.t * Constant.t * Constant.t -> (* name of the function, the functional and the fixpoint equation *)
  Indfun_common.tcc_lemma_value ref -> (* a pointer to the obligation proofs lemma *)
  bool -> (* is that function uses measure *)
  int -> (* the number of recursive argument *)
  EConstr.types -> (* the type of the recursive argument *)
  EConstr.constr -> (* the wf relation used to prove the function *)
  Tacmach.tactic


(* val is_pte  : rel_declaration -> bool  *)
