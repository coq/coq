Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Goal forall A B (p : prod A B), p = let (x, y) := p in pair A B x y.
Proof.
  intros A B p.
  exact eq_refl.
Qed.
