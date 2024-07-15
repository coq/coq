Scheme foo := Elimination for nat Sort Prop.

Fail Check eq_refl : foo = nat_ind.

Check foo : forall P : nat -> Prop, P 0 -> (forall n : nat, P (S n)) -> forall n : nat, P n.

Scheme bar := Case for nat Sort Prop.

Check bar : forall P : Prop, P -> (nat -> P) -> nat -> P.

Inductive even (x: nat): nat -> Prop :=
  | even_base: even x O
  | even_succ: forall n, odd x n -> even x (S n)

with odd (x: nat): nat -> Prop :=
  | odd_succ: forall n, even x n -> odd x (S n).

(* mutual nonrecursive schemes is nonsense so rejected *)
Fail Scheme even_case := Case for even Sort Prop
    with odd_case := Case for odd Sort Prop.
