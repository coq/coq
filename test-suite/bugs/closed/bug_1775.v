Axiom pair : nat -> nat -> nat -> Prop.
Axiom pl : (nat -> Prop) -> (nat -> Prop) -> (nat -> Prop).
Axiom plImp : forall k P Q,
  pl P Q k -> forall (P':nat -> Prop),
    (forall k', P k' -> P' k') -> forall (Q':nat -> Prop),
      (forall k', Q k' -> Q' k') ->
      pl P' Q' k.

Definition nexists (P:nat -> nat -> Prop) : nat -> Prop :=
  fun k' => exists k, P k k'.

Goal forall s k k' m,
  (pl k' (nexists (fun w => (nexists (fun b => pl (pair w w)
    (pl (pair s b)
    (nexists (fun w0 => (nexists (fun a => pl (pair b w0)
      (nexists (fun w1 => (nexists (fun c => pl
        (pair a w1) (pl (pair a c) k))))))))))))))) m.
intros.
eapply plImp; [ | eauto | intros ].
2:econstructor.
2:econstructor.
2:eapply plImp; [ | eauto | intros ].
3:eapply plImp; [ | eauto | intros ].
4:econstructor.
4:econstructor.
4:eapply plImp; [ | eauto | intros ].
5:econstructor.
5:econstructor.
5:eauto.
4:eauto.
3:eauto.
2:eauto.

assert (X := 1).
clear X.   (* very slow! *)

simpl.  (* exception Not_found *)

Admitted.
