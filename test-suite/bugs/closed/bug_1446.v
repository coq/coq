Lemma not_true_eq_false : forall (b:bool), b <> true -> b = false.
Proof.
 destruct b;intros;trivial.
 elim H.
 exact (refl_equal true).
Qed.

Section BUG.

 Variable b : bool.
 Hypothesis H  : b <> true.
 Hypothesis H0 : b = true.
 Hypothesis H1 : b <> true.

 Goal False.
  rewrite (not_true_eq_false _ H) in * |-.
  contradiction.
 Qed.

End BUG.
