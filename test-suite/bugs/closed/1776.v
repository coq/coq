Axiom pair : nat -> nat -> nat -> Prop.
Axiom pl : (nat -> Prop) -> (nat -> Prop) -> (nat -> Prop).
Axiom plImpR : forall k P Q,
  pl P Q k -> forall (Q':nat -> Prop),
    (forall k', Q k' -> Q' k') ->
    pl P Q' k.

Definition nexists (P:nat -> nat -> Prop) : nat -> Prop :=
  fun k' => exists k, P k k'.

Goal forall a A m,
  True ->
  (pl A (nexists (fun x => (nexists
    (fun y => pl (pair a (S x)) (pair a (S y))))))) m.
Proof.
  intros.
  eapply plImpR; [ | intros; econstructor; econstructor; eauto].
  clear H;
    match goal with
       | |- (pl _ (pl (pair _ ?x) _)) _ => replace x with 0
    end.
Admitted.
