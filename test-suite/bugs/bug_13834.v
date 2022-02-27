Inductive myeq (A : Type) (x : A) : A -> Prop :=
| myeq_refl : myeq A x x.

Arguments myeq [A].
Arguments myeq_refl {A} {x}.

Definition myeqss (A : Type) (a b : A) (H : myeq (Some a) (Some b)) : myeq a b.
Proof.
  pose (Some b) as Someb.
  rewrite (myeq_refl : myeq (Some b) Someb) in *.
  rewrite (myeq_refl : myeq b (match Someb with None => a | Some b_ => b_ end)).
  destruct H.
  reflexivity.
Qed.
