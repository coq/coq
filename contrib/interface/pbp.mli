val pbp_tac : (Tacexpr.raw_tactic_expr -> 'a) ->
    Names.identifier option -> int list ->
    Proof_type.goal Tacmach.sigma ->
    Proof_type.goal list Proof_type.sigma * Proof_type.validation;;
