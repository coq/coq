val blast_tac : (Tacexpr.raw_tactic_expr -> 'a) ->
    int list ->
    Proof_type.goal Tacmach.sigma ->
    Proof_type.goal list Proof_type.sigma * Proof_type.validation;;

