Module a.
  Local Hint Extern 0 => progress subst.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    (* this should not fail *)
    progress eauto.
  Defined.
End a.

Module b.
  Local Hint Extern 0 => progress subst.
  Goal forall T (x y : T) (P Q : _ -> Prop), y = x -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    eauto.
  Defined.
End b.

Module c.
  Local Hint Extern 0 => progress subst; eauto.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    eauto.
  Defined.
End c.

Module d.
  Local Hint Extern 0 => progress subst; repeat match goal with H : _ |- _ => revert H end.
  Goal forall T (x y : T) (P Q : _ -> Prop), x = y -> (P x -> Q x) -> P y -> Q y.
  Proof.
    intros.
    debug eauto.
  Defined.
End d.
