Fixpoint F (n : nat) (A : Type) : Type :=
  match n with
  | 0 => True
  | S n => forall (x : A), F n (x = x)
  end.

Goal forall A n, (forall (x : A) (e : x = x), F n (e = e)).
intros A n.
Fail change (forall x, F n (x = x)) with (F (S n)).
