Set Automatic Introduction.

Inductive even : nat -> Prop :=
| even_0 : even 0
| even_odd : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd_1 : odd 1
| odd_even : forall n, even n -> odd (S n).

Lemma foo {n : nat} (E : even n) : even (S (S n))
with bar {n : nat} (O : odd n) : odd (S (S n)).
Proof. destruct E. constructor. constructor. apply even_odd. apply (bar _ H).
  destruct O. repeat constructor. apply odd_even. apply (foo _ H).
Defined.

