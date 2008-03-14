Require Export QArith.
Require Export Qreduction.

Hint Resolve Qlt_le_weak : qarith.

Definition Qabs (x:Q) := let (n,d):=x in (Zabs n#d).

Lemma Qabs_case : forall (x:Q) (P : Q -> Type), (0 <= x -> P x) -> (x <= 0 -> P (- x)) -> P (Qabs x).
Proof.
intros x P H1 H2.
destruct x as [[|xn|xn] xd];
[apply H1|apply H1|apply H2];
abstract (compute; discriminate).
Defined.

Add Morphism Qabs with signature Qeq ==> Qeq as Qabs_wd.
intros [xn xd] [yn yd] H.
simpl.
unfold Qeq in *.
simpl in *.
change (' yd)%Z with (Zabs (' yd)).
change (' xd)%Z with (Zabs (' xd)).
repeat rewrite <- Zabs_Zmult.
congruence.
Qed.

Lemma Qabs_pos : forall x, 0 <= x -> Qabs x == x.
Proof.
intros x H.
apply Qabs_case.
reflexivity.
intros H0.
setoid_replace x with 0.
reflexivity.
apply Qle_antisym; assumption.
Qed.

Lemma Qabs_neg : forall x, x <= 0 -> Qabs x == - x.
Proof.
intros x H.
apply Qabs_case.
intros H0.
setoid_replace x with 0.
reflexivity.
apply Qle_antisym; assumption.
reflexivity.
Qed.

Lemma Qabs_nonneg : forall x, 0 <= (Qabs x).
intros x.
apply Qabs_case.
auto.
apply (Qopp_le_compat x 0).
Qed.

Lemma Zabs_Qabs : forall n d, (Zabs n#d)==Qabs (n#d).
Proof.
intros [|n|n]; reflexivity.
Qed.

Lemma Qabs_opp : forall x, Qabs (-x) == Qabs x.
Proof.
intros x.
do 2 apply Qabs_case; try (intros; ring);
(intros H0 H1;
setoid_replace x with 0;[reflexivity|];
apply Qle_antisym);try assumption;
rewrite Qle_minus_iff in *;
ring_simplify;
ring_simplify in H1;
assumption.
Qed.

Lemma Qabs_triangle : forall x y, Qabs (x+y) <= Qabs x + Qabs y.
Proof.
intros [xn xd] [yn yd].
unfold Qplus.
unfold Qle.
simpl.
apply Zmult_le_compat_r;auto with *.
change (' yd)%Z with (Zabs (' yd)).
change (' xd)%Z with (Zabs (' xd)).
repeat rewrite <- Zabs_Zmult.
apply Zabs_triangle.
Qed.

Lemma Qabs_Qmult : forall a b, Qabs (a*b) == (Qabs a)*(Qabs b).
Proof.
intros [an ad] [bn bd].
simpl.
rewrite Zabs_Zmult.
reflexivity.
Qed.

Lemma Qle_Qabs : forall a, a <= Qabs a.
Proof.
intros a.
apply Qabs_case; auto with *.
intros H.
apply Qle_trans with 0; try assumption.
change 0 with (-0).
apply Qopp_le_compat.
assumption.
Qed.

Lemma Qabs_triangle_reverse : forall x y, Qabs x - Qabs y <= Qabs (x - y).
Proof.
intros x y.
rewrite Qle_minus_iff.
setoid_replace (Qabs (x - y) + - (Qabs x - Qabs y)) with ((Qabs (x - y) + Qabs y) + - Qabs x) by ring.
rewrite <- Qle_minus_iff.
setoid_replace (Qabs x) with (Qabs (x-y+y)).
apply Qabs_triangle.
apply Qabs_wd.
ring.
Qed.
