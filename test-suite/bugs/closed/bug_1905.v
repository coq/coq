
Require Import Setoid Program.

Axiom t : Set.
Axiom In : nat -> t -> Prop.
Axiom InE : forall (x : nat) (s:t), impl (In x s) True.

Goal forall a s,
 In a s -> False.
Proof.
 intros a s Ia.
 rewrite InE in Ia.
Admitted.
