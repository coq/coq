
val report_error : Tacexpr.raw_tactic_expr ->
    Proof_type.goal Proof_type.sigma option ref ->
    Tacexpr.raw_tactic_expr ref -> int list ref -> int list -> Tacmach.tactic;;

val clean_path : Tacexpr.raw_tactic_expr -> int list -> int list;;
