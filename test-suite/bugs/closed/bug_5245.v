Set Primitive Projections.

Record foo := Foo {
  foo_car : Type;
  foo_rel : foo_car -> foo_car -> Prop
}.
Arguments foo_rel : simpl never.

Definition foo_fun {A B} := Foo (A -> B) (fun f g => forall x, f x = g x).

Goal @foo_rel foo_fun (fun x : nat => x) (fun x => x).
Proof.
intros x; exact eq_refl.
Undo.
progress hnf; intros; exact eq_refl.
Undo.
unfold foo_rel. intros x. exact eq_refl.
Qed.
