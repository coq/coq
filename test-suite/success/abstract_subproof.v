
Axiom foo : nat -> bool -> nat.

Lemma bar : nat.
Proof.
  apply foo.
  abstract:{
    exact 0.
  }
  exact true.
Defined.

Fail Check eq_refl : bar = foo 0 true.

Check eq_refl : bar = foo _ true.

Check bar_subproof : nat.

Lemma baz : nat.
Proof.
  abstract:{
    shelve.
    Fail }
    Unshelve.
    exact 0.
  }
Qed.

Lemma bii : forall x, x = 0 + x.
Proof.
  intros x.
  abstract:{ reflexivity. }
Qed.
