Inductive T (A : Type) := tt.

Universe u.

Lemma dummy : forall (A : Type@{u}), T A.
Proof.
intros; apply tt.
Qed.

Constraint T.u0 < u. (* Check that there is no constraint u <= T.u0 *)
