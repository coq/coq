Parameter monotonic : forall {A B} (leA : A -> A -> Prop) (leB : B -> B -> Prop),
  (A -> B) -> Prop.

Axiom monotonic_cst : forall A B (leA : A -> A -> Prop) (leB : B -> B -> Prop),
  forall (b:B), monotonic leA leB (fun _ : A => b).

#[local] Hint Extern 0 (monotonic _ _ (fun _ => ?x)) =>
  simple apply monotonic_cst : mymonotonic.

Parameter (foo : nat -> nat).

Goal (forall a, monotonic le le (fun _ => foo a)).
Proof.
  typeclasses eauto with mymonotonic.
Qed.

#[local] Hint Extern 999999 (monotonic _ _ _) => shelve : mymonotonic.

Goal (forall a, monotonic le le (fun _ => foo a)).
Proof.
  unshelve typeclasses eauto with mymonotonic.
Qed.
