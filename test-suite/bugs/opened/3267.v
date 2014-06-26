Module a.
  Hint Extern 0 => progress subst.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    (* this should not fail *)
    Fail progress eauto.
    admit.
  Defined.
End a.

Module b.
  Hint Extern 0 => progress subst.
  Goal forall T (x y : T) (P Q : _ -> Prop), y = x -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    eauto.
  Defined.
End b.

Module c.
  Hint Extern 0 => progress subst; eauto.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    eauto.
  Defined.
End c.

Module d.
  Hint Extern 0 => progress subst; repeat match goal with H : _ |- _ => revert H end.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    eauto.
  Defined.
End d.
