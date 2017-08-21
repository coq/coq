Require Import Setoid.

Parameter recursion : forall A : Set, A -> (nat -> A -> A) -> nat -> A.

Axiom recursion_S :
  forall (A : Set) (EA : relation A) (a : A) (f : nat -> A -> A) (n : nat),
    EA (recursion A a f (S n)) (f n (recursion A a f n)).

Goal forall n : nat, recursion nat 0 (fun _ _ => 1) (S n) = 1.
intro n.
rewrite recursion_S.
reflexivity.
Qed.

Goal forall n : nat, recursion nat 0 (fun _ _ => 1) (S n) = 1.
intro n.
setoid_rewrite recursion_S.
reflexivity.
Qed.
