Polymorphic Inductive T:Type := t.
Polymorphic Definition general_ok (pre: T -> Prop) := forall v, pre v.
Polymorphic Definition ok := general_ok (fun _ => True).

Definition ok' := True.

Theorem ok_equiv : ok <-> ok'.
  unfold ok, ok', general_ok.
  intuition.
Qed.

Corollary ok_equiv' (H:ok) : False.
Proof.
  destruct ok_equiv; intuition.
  try match goal with
      | [ H: _ -> _, H': _ |- _ ] =>
        specialize (H H'); fail 10 "bad"
      end.
Abort.
