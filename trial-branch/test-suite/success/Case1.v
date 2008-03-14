(* Testing eta-expansion of elimination predicate *)

Section NATIND2.
Variable P : nat -> Type.
Variable H0 : P 0.
Variable H1 : P 1.
Variable H2 : forall n : nat, P n -> P (S (S n)).
Fixpoint nat_ind2 (n : nat) : P n :=
  match n as x return (P x) with
  | O => H0
  | S O => H1
  | S (S n) => H2 n (nat_ind2 n)
  end.
End NATIND2.

