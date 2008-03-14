val pbp_tac : (Tacexpr.raw_tactic_expr -> 'a) ->
    Names.identifier option -> int list -> Proof_type.tactic
