
val report_error : Tacexpr.glob_tactic_expr ->
    Proof_type.goal Evd.sigma option ref ->
    Tacexpr.glob_tactic_expr ref -> int list ref -> int list -> Tacmach.tactic;;

val clean_path : Tacexpr.glob_tactic_expr -> int list -> int list;;
