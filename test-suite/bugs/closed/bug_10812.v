(* subst with indirectly dependent section variables *)

Section A.

Variable a:nat.
Definition b := a.

Goal a=1 -> a+a=1 -> b=1.
intros.
Fail subst a. (* was working; we make it failing *)
rewrite H in H0.
discriminate.
Qed.

Goal a=1 -> a+a=1 -> b=1.
intros.
subst. (* should not apply to a *)
rewrite H in H0.
discriminate.
Qed.

Goal forall t, a=t -> b=t.
intros.
subst.
reflexivity.
Qed.

End A.
