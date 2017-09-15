Goal forall x:nat, (forall x, x=0 -> True)->True.
  intros; eapply H.
  instantiate (1:=(fun y => _) (S x)).
  simpl.
  clear x. trivial.
Qed.

Goal forall y z, (forall x:nat, x=y -> True) -> y=z -> True.
  intros; eapply H.
  rename z into z'.
  clear H0.
  clear z'.
  reflexivity.
Qed.

Class A.

Section Foo.

  Variable a : A.

  Goal A.
    solve [typeclasses eauto].
    Undo 1.
    clear a.
    try typeclasses eauto.
    assert(a:=Build_A).
    solve [ typeclasses eauto ].
    Undo 2.
    assert(b:=Build_A).
    solve [ typeclasses eauto ].
  Qed.
End Foo.
