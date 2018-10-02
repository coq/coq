Definition f  (n:nat) := n = n.

Lemma f_refl : forall n , f n.
intros. reflexivity.
Qed.

Definition f'  (x:nat) (n:nat) := n = n.

Lemma f_refl' : forall n , f' n n.
Proof.
 intros. reflexivity.
Qed.

Require Import ZArith.

Definition f'' (a:bool) := if a then eq (A:= Z) else Z.lt.

Lemma f_refl'' : forall n , f'' true n n.
Proof.
 intro. reflexivity.
Qed.
