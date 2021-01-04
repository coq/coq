Inductive foo (x := tt) := Foo : forall (y := x), foo.

Definition get (t : foo) := match t with Foo _ y => y end.

Goal get Foo = tt.
Proof.
reflexivity.
Qed.

Goal forall x : foo,
  match x with Foo _ y => y end = match x with Foo _ _ => tt end.
Proof.
intros.
reflexivity.
Qed.
