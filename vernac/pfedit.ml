(* Compat API / *)
let get_current_context = Declare.get_current_context
let solve = Proof.solve
let by = Declare.by
let refine_by_tactic = Proof.refine_by_tactic

(* We don't want to export this anymore, but we do for now *)
let build_by_tactic = Declare.build_by_tactic
let build_constant_by_tactic = Declare.build_constant_by_tactic
