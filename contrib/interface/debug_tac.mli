
val report_error : Coqast.t ->
    Proof_type.goal Proof_type.sigma option ref ->
    Coqast.t ref -> int list ref -> int list -> Tacmach.tactic;;

val clean_path : int -> Coqast.t -> int list -> int list;;
