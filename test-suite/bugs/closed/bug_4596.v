Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.

Definition T (x : bool) := x = true.

Goal forall (S : Type) (b b0 : S -> nat -> bool) (str : S) (p : nat)
  (s : forall n : nat, bool)
  (s0 s1 : nat -> S -> S),
  (forall (str0 : S) (n m : nat),
  (if s m then T (b0 (s1 n str0) 0) else T (b (s1 n str0) 0)) -> T (b (s0 n str0) m) ->
    T (b str0 m)) ->
  T (b str p).
Proof.
intros ???????? H0.
rewrite H0.
