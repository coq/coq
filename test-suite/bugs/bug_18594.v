Set Universe Polymorphism.

Lemma foo@{s| |} (A:Type@{s|Set}) (a:A) : A.
Proof.
  exact a.
Qed.

Definition bar : foo nat = foo (id nat) := eq_refl.

Fail Definition baz x y : foo nat x = foo nat y := eq_refl.

Definition baz' (A:SProp) (f:A->nat) x y : f (foo A x) = f (foo A y) := eq_refl.
