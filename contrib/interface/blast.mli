val blast_tac : (Ctast.t -> 'a) ->
    Proof_type.tactic_arg list ->
    Proof_type.goal Tacmach.sigma ->
    Proof_type.goal list Proof_type.sigma * Proof_type.validation;;

