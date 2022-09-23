Create HintDb db.
Parameter P : unit -> unit -> Prop.
Axiom HP : forall b, P b (id b).

#[local] Hint Resolve HP | 0 (P tt tt) : db.

Goal P tt tt.
Proof.
  Succeed solve [simple apply HP].
  solve [auto with db].
Qed.
