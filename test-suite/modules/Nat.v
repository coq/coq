Definition T:=nat.

Definition le:=Peano.le.

Hints Unfold le.

Lemma le_refl:(n:nat)(le n n).
  Auto.
Save.

Lemma le_trans:(n,m,k:nat)(le n m) -> (le m k) -> (le n k).
  Unfold le.
  Intros.
  Generalize H.
  Clear H.
  Elim H0.
  Auto.
  Auto.  
Save.

Lemma le_mono_S : (n,m:nat)(le n m) -> (le (S n) (S m)).
  Unfold le.
  NewInduction 1.
  Auto.
  Auto.
Save.

Hints Resolve le_mono_S.

Lemma le_pred_mono : (n,m:nat) (le n m) -> (le (pred n) (pred m)).
  Unfold le.
  Induction 1.
  Auto.
  Intro.
  Case m0.
  Auto.
  Intro.
  Simpl.
  Auto.
Save.

Hints Resolve le_pred_mono.  

Lemma le_S_mono : (m,n:nat)(le (S n) (S m)) -> (le n m).
  Intros.
  Change (le (pred (S n)) (pred (S m))).
  Auto.
Save.

Hints Resolve le_S_mono.

Lemma le_antis:(n,m:nat)(le n m) -> (le m n) -> n=m.
  NewInduction n.
  Intros.
  Inversion H0.
  Reflexivity.

  Intros.
  Inversion H.
  Auto.
  Rewrite (IHn m0).
  Auto.
  Rewrite <- H2 in H.
  Auto.
  Rewrite <- H2 in H0.
  Auto.
Save.

