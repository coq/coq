Definition T:=nat.

Definition le:=Peano.le.

Hints Unfold le.

Lemma le_refl:(n:nat)(le n n).
  Auto.
Qed.

Require Le.

Lemma le_trans:(n,m,k:nat)(le n m) -> (le m k) -> (le n k).
  EAuto with arith.
Qed.

Lemma le_antis:(n,m:nat)(le n m) -> (le m n) -> n=m.
  EAuto with arith.
Qed.
