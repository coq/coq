
Section Foo.
Variable A : Type.
Lemma foo : A -> True. now intros _. Qed.
Goal Type -> True.
rename A into B.
intros A.
Fail apply foo.
