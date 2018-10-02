(* Test coercion from ident to evaluable reference *)
Tactic Notation "unfold_hyp" hyp(H) := cbv delta [H].
Goal True -> Type.
  intro H''.
  Fail unfold_hyp H''.
