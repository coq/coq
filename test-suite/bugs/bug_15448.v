Lemma bar (a b:unit) (H0: a = b) (H: a = b) : a = b.
Proof.
  Fail rewrite (match a,b return _ -> a = b with tt, tt => fun _ => eq_refl end H) in H,H0.
  Fail rewrite (match a,b return _ -> a = b with tt, tt => fun _ => eq_refl end H0) in H,H0.
  rewrite (match a,b return _ -> a = b with tt, tt => fun _ => eq_refl end H) in H0.
  Check H0 : b = b.
  Check H : a = b.
  destruct a,b;reflexivity.
Defined.

Lemma bar' (a b:unit) (H0: a = b) (H: a = b) : a = b.
Proof.
  rewrite (match a,b return _ -> a = b with tt, tt => fun _ => eq_refl end H) in *.
  Check H0 : b = b.
  Check H : a = b.
  destruct a,b;reflexivity.
Defined.

Lemma bar'' (a b:unit) (H0: a = b) (H: a = b) : a = b.
Proof.
  unshelve erewrite (_: a = b) in *.
  { Fail revert H. destruct a,b;reflexivity. }
  destruct a,b;reflexivity.
Defined.
