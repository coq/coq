Axiom pl : (nat -> Prop) -> (nat -> Prop) -> (nat -> Prop).
Axiom plImp : forall k P Q,
  pl P Q k -> forall (P':nat -> Prop),
    (forall k', P k' -> P' k') -> forall (Q':nat -> Prop),
      (forall k', Q k' -> Q' k') ->
      pl P' Q' k.

Definition nexists (P:nat -> nat -> Prop) : nat -> Prop :=
  fun k' => exists k, P k k'.

Goal forall k (A:nat -> nat -> Prop) (B:nat -> Prop),
  pl (nexists A) B k.
intros.
eapply plImp.
2:intros m' M'; econstructor; apply M'.
2:intros m' M'; apply M'.
simpl.
Admitted.
