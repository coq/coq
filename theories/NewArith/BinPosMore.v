Require Import BinPos.
Require Import Prelude.

Open Local Scope positive_scope.

Theorem double_distr_plus : forall m n : positive, xO (m + n) = xO m + xO n.
Proof.
destruct n; destruct m; simpl; auto.
Qed.

Theorem Ptimes_Sn_m : forall n m : positive, (Psucc n) * m = m + n * m.
Proof.
induction n as [n IH | n IH |]; simpl; intro m.
rewrite IH; rewrite Pplus_assoc; rewrite Pplus_diag;
rewrite <- double_distr_plus; reflexivity.
reflexivity.
symmetry; apply Pplus_diag.
Qed.

Theorem Pcompare_eq_Lt :
 forall p q : positive, (p ?= q) Eq = Lt <-> (p ?= q) Gt = Lt.
Proof.
intros p q; split; [| apply Pcompare_Gt_Lt].
generalize q; clear q; induction p; induction q; simpl; auto.
intro; discriminate.
Qed.

Theorem Pcompare_eq_Gt :
  forall p q : positive, (p ?= q) Eq = Gt <-> (p ?= q) Lt = Gt.
Proof.
intros p q; split; [| apply Pcompare_Lt_Gt].
generalize q; clear q; induction p; induction q; simpl; auto.
intro; discriminate.
Qed.

Theorem Pcompare_refl_id : forall (p : positive) (r : comparison), (p ?= p) r = r.
induction p; auto.
Qed.

Theorem Pcompare_Lt_eq_Lt :
 forall p q:positive, (p ?= q) Lt = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
intros p q; split.
apply Pcompare_Lt_Lt.
intro H; destruct H as [H | H]; [ | rewrite H; apply Pcompare_refl_id].
generalize q H. clear q H.
induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H;
try (reflexivity || assumption || discriminate H); apply IH; assumption.
Qed.

Theorem Pcompare_Gt_eq_Gt :
 forall p q:positive, (p ?= q) Gt = Gt <-> (p ?= q) Eq = Gt \/ p = q.
Proof.
intros p q; split.
generalize q; clear q;
induction p as [p IHp| p IHp| ]; destruct q as [q| q| ];
simpl; auto; try discriminate; intro H2; elim (IHp q H2);
auto; intros E; rewrite E; auto.
intro H; destruct H as [H | H]; [ | rewrite H; apply Pcompare_refl_id].
generalize q H. clear q H.
induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H;
try (reflexivity || assumption || discriminate H); apply IH; assumption.
Qed.

Theorem Pcompare_p_Sp : forall p : positive, (p ?= Psucc p) Eq = Lt.
Proof.
induction p as [p' IH | p' IH |]; simpl in *;
[apply -> Pcompare_eq_Lt; assumption | apply Pcompare_refl_id | reflexivity].
Qed.

Theorem Pcompare_1 : forall p, ~ (p ?= 1) Eq = Lt.
Proof.
destruct p; discriminate.
Qed.

Theorem Pcompare_p_Sq : forall p q : positive,
  (p ?= Psucc q) Eq = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
intros p q; split.
generalize p q; clear p q.
induction p as [p' IH | p' IH |]; destruct q as [q' | q' |]; simpl; intro H.
assert (T : xI p' = xI q' <-> p' = q').
split; intro HH; [inversion HH; trivial | rewrite HH; reflexivity].
cut ((p' ?= q') Eq = Lt \/ p' = q'). firstorder.
apply IH. apply Pcompare_Gt_Lt; assumption.
left; apply -> Pcompare_eq_Lt; assumption.
destruct p'; discriminate.
apply IH in H. left.
destruct H as [H | H]; [apply <- Pcompare_Lt_eq_Lt; left; assumption |
rewrite H; apply Pcompare_refl_id].
assert (T : xO p' = xO q' <-> p' = q').
split; intro HH; [inversion HH; trivial | rewrite HH; reflexivity].
cut ((p' ?= q') Eq = Lt \/ p' = q'); [firstorder | ].
apply -> Pcompare_Lt_eq_Lt; assumption.
destruct p'; discriminate.
left; reflexivity.
left; reflexivity.
right; reflexivity.
intro H; destruct H as [H | H].
generalize q H; clear q H. induction p as [p' IH | p' IH |];
destruct q as [q' | q' |]; simpl in *; intro H;
try (reflexivity || discriminate H).
apply -> Pcompare_eq_Lt; apply IH; assumption.
apply <- Pcompare_eq_Lt; assumption.
assert (H1 : (p' ?= q') Eq = Lt \/ p' = q'); [apply -> Pcompare_Lt_eq_Lt; assumption |].
destruct H1 as [H1 | H1]; [apply IH; assumption | rewrite H1; apply Pcompare_p_Sp].
apply <- Pcompare_Lt_eq_Lt; left; assumption.
rewrite H; apply Pcompare_p_Sp.
Qed.

Close Local Scope positive_scope.
