Inductive even (x: nat): nat -> Prop :=
  | even_base: even x O
  | even_succ: forall n, odd x n -> even x (S n)

with odd (x: nat): nat -> Prop :=
  | odd_succ: forall n, even x n -> odd x (S n).

Scheme even_ind2 := Minimality for even Sort Prop
  with odd_ind2 := Minimality for odd Sort Prop.

Combined Scheme even_odd_ind from even_ind2, odd_ind2.

Check (even_odd_ind :forall (x : nat) (P P0 : nat -> Prop),
  P 0 ->
  (forall n : nat, odd x n -> P0 n -> P (S n)) ->
  (forall n : nat, even x n -> P n -> P0 (S n)) ->
  (forall n : nat, even x n -> P n) /\ (forall n : nat, odd x n -> P0 n)).
