Require Export NZBase.

Module Type NZOrderSig.
Declare Module Export NZBaseMod : NZBaseSig.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.

Axiom NZlt_wd : rel_wd NZE NZE NZlt.
Axiom NZle_wd : rel_wd NZE NZE NZle.

Notation "x < y" := (NZlt x y).
Notation "x <= y" := (NZle x y).

Axiom NZle__lt_or_eq : forall n m : NZ, n <= m <-> n < m \/ n == m.
Axiom NZlt_irrefl : forall n : NZ, ~ (n < n).
Axiom NZlt_succ__le : forall n m : NZ, n < S m <-> n <= m.
End NZOrderSig.

Module NZOrderPropFunct (Import NZOrderMod : NZOrderSig).
Module Export NZBasePropMod := NZBasePropFunct NZBaseMod.

Ltac NZle_intro1 := rewrite NZle__lt_or_eq; left.
Ltac NZle_intro2 := rewrite NZle__lt_or_eq; right.
Ltac NZle_elim H := rewrite NZle__lt_or_eq in H; destruct H as [H | H].

Add Morphism NZlt with signature NZE ==> NZE ==> iff as NZlt_morph.
Proof.
exact NZlt_wd.
Qed.

Add Morphism NZle with signature NZE ==> NZE ==> iff as NZle_morph.
Proof.
exact NZle_wd.
Qed.

Lemma NZlt_stepl : forall x y z : NZ, x < y -> x == z -> z < y.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZlt_stepr : forall x y z : NZ, x < y -> y == z -> x < z.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZle_stepl : forall x y z : NZ, x <= y -> x == z -> z <= y.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Lemma NZle_stepr : forall x y z : NZ, x <= y -> y == z -> x <= z.
Proof.
intros x y z H1 H2; now rewrite <- H2.
Qed.

Declare Left  Step NZlt_stepl.
Declare Right Step NZlt_stepr.
Declare Left  Step NZle_stepl.
Declare Right Step NZle_stepr.

Theorem NZlt_le_incl : forall n m : NZ, n < m -> n <= m.
Proof.
intros; now NZle_intro1.
Qed.

Theorem NZlt_neq : forall n m : NZ, n < m -> n ~= m.
Proof.
intros n m H1 H2; rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZle_refl : forall n : NZ, n <= n.
Proof.
intro; now NZle_intro2.
Qed.

Theorem NZlt_succ_r : forall n : NZ, n < S n.
Proof.
intro n. rewrite NZlt_succ__le. now NZle_intro2.
Qed.

Theorem NZle_succ_r : forall n : NZ, n <= S n.
Proof.
intro; NZle_intro1; apply NZlt_succ_r.
Qed.

Theorem NZlt__lt_succ : forall n m : NZ, n < m -> n < S m.
Proof.
intros. rewrite NZlt_succ__le. now NZle_intro1.
Qed.

Theorem NZle__le_succ : forall n m : NZ, n <= m -> n <= S m.
Proof.
intros n m H; rewrite <- NZlt_succ__le in H; now NZle_intro1.
Qed.

Theorem NZle_succ__le_or_eq_succ : forall n m : NZ, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite NZle__lt_or_eq. now rewrite NZlt_succ__le.
Qed.

(** A corollary of having an order is that NZ is infinite *)

(* This section about infinity of NZ relies on the type nat and can be
safely removed *)

Definition succ_iter (n : nat) (m : NZ) :=
  nat_rec (fun _ => NZ) m (fun _ l => S l) n.

Theorem NZlt_succ_iter_r :
  forall (n : nat) (m : NZ), m < succ_iter (Datatypes.S n) m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply NZlt_succ_r. now apply NZlt__lt_succ.
Qed.

Theorem NZneq_succ_iter_l :
  forall (n : nat) (m : NZ), succ_iter (Datatypes.S n) m ~= m.
Proof.
intros n m H. pose proof (NZlt_succ_iter_r n m) as H1. rewrite H in H1.
false_hyp H1 NZlt_irrefl.
Qed.

(* End of the section about the infinity of NZ *)

(* The following theorem is a special case of NZneq_succ_iter_l, but we
prove it independently *)

Theorem NZneq_succ_l : forall n : NZ, S n ~= n.
Proof.
intros n H. pose proof (NZlt_succ_r n) as H1. rewrite H in H1.
false_hyp H1 NZlt_irrefl.
Qed.

Theorem NZnlt_succ_l : forall n : NZ, ~ S n < n.
Proof.
intros n H; apply NZlt__lt_succ in H. false_hyp H NZlt_irrefl.
Qed.

Theorem NZnle_succ_l : forall n : NZ, ~ S n <= n.
Proof.
intros n H; NZle_elim H.
false_hyp H NZnlt_succ_l. false_hyp H NZneq_succ_l.
Qed.

Theorem NZlt__le_succ : forall n m : NZ, n < m <-> S n <= m.
Proof.
intro n; NZinduct_center m n.
rewrite_false (n < n) NZlt_irrefl. now rewrite_false (S n <= n) NZnle_succ_l.
intro m. rewrite NZlt_succ__le. rewrite NZle_succ__le_or_eq_succ.
rewrite NZsucc_inj_wd. rewrite (NZle__lt_or_eq n m).
rewrite or_cancel_r.
apply NZlt_neq.
intros H1 H2; rewrite H2 in H1; false_hyp H1 NZnle_succ_l.
reflexivity.
Qed.

Theorem NZlt_succ__lt : forall n m : NZ, S n < m -> n < m.
Proof.
intros n m H; apply <- NZlt__le_succ; now NZle_intro1.
Qed.

Theorem NZle_succ__le : forall n m : NZ, S n <= m -> n <= m.
Proof.
intros n m H; NZle_intro1; now apply <- NZlt__le_succ.
Qed.

Theorem NZsucc_lt_mono : forall n m : NZ, n < m <-> S n < S m.
Proof.
intros n m. rewrite NZlt__le_succ. symmetry. apply NZlt_succ__le.
Qed.

Theorem NZsucc_le_mono : forall n m : NZ, n <= m <-> S n <= S m.
Proof.
intros n m. do 2 rewrite NZle__lt_or_eq.
rewrite <- NZsucc_lt_mono; now rewrite NZsucc_inj_wd.
Qed.

Theorem NZlt_lt_false : forall n m, n < m -> m < n -> False.
Proof.
intros n m; NZinduct_center n m.
intros H _; false_hyp H NZlt_irrefl.
intro n; split; intros H H1 H2.
apply NZlt_succ__lt in H1. apply -> NZlt_succ__le in H2. NZle_elim H2.
now apply H. rewrite H2 in H1; false_hyp H1 NZlt_irrefl.
apply NZlt__lt_succ in H2. apply -> NZlt__le_succ in H1. NZle_elim H1.
now apply H. rewrite H1 in H2; false_hyp H2 NZlt_irrefl.
Qed.

Theorem NZlt_asymm : forall n m, n < m -> ~ m < n.
Proof.
intros n m; unfold not; apply NZlt_lt_false.
Qed.

Theorem NZlt_trans : forall n m p : NZ, n < m -> m < p -> n < p.
Proof.
intros n m p; NZinduct_center p m.
intros _ H; false_hyp H NZlt_irrefl.
intro p. do 2 rewrite NZlt_succ__le.
split; intros H H1 H2.
NZle_intro1; NZle_elim H2; [now apply H | now rewrite H2 in H1].
assert (n <= p) as H3. apply H. assumption. now NZle_intro1.
NZle_elim H3. assumption. rewrite <- H3 in H2. elimtype False.
now apply (NZlt_lt_false n m).
Qed.

Theorem NZle_trans : forall n m p : NZ, n <= m -> m <= p -> n <= p.
Proof.
intros n m p H1 H2; NZle_elim H1.
NZle_elim H2. NZle_intro1; now apply NZlt_trans with (m := m).
NZle_intro1; now rewrite <- H2. now rewrite H1.
Qed.

Theorem NZle_lt_trans : forall n m p : NZ, n <= m -> m < p -> n < p.
Proof.
intros n m p H1 H2; NZle_elim H1.
now apply NZlt_trans with (m := m). now rewrite H1.
Qed.

Theorem NZlt_le_trans : forall n m p : NZ, n < m -> m <= p -> n < p.
Proof.
intros n m p H1 H2; NZle_elim H2.
now apply NZlt_trans with (m := m). now rewrite <- H2.
Qed.

Theorem NZle_antisym : forall n m : NZ, n <= m -> m <= n -> n == m.
Proof.
intros n m H1 H2; now (NZle_elim H1; NZle_elim H2);
[elimtype False; apply (NZlt_lt_false n m) | | |].
Qed.

(** Trichotomy, decidability, and double negation elimination *)

Theorem NZlt_trichotomy : forall n m : NZ,  n < m \/ n == m \/ m < n.
Proof.
intros n m; NZinduct_center n m.
right; now left.
intro n; rewrite NZlt_succ__le. stepr ((S n < m \/ S n == m) \/ m <= n) by tauto.
rewrite <- (NZle__lt_or_eq (S n) m). symmetry (n == m).
stepl (n < m \/ m < n \/ m == n) by tauto. rewrite <- NZle__lt_or_eq.
apply or_iff_compat_r. apply NZlt__le_succ.
Qed.

Theorem NZle_lt_dec : forall n m : NZ, n <= m \/ m < n.
Proof.
intros n m; destruct (NZlt_trichotomy n m) as [H | [H | H]].
left; now NZle_intro1. left; now NZle_intro2. now right.
Qed.

Theorem NZle_nlt : forall n m : NZ, n <= m <-> ~ m < n.
Proof.
intros n m. split; intro H; [intro H1 |].
eapply NZle_lt_trans in H; [| eassumption ..]. false_hyp H NZlt_irrefl.
destruct (NZle_lt_dec n m) as [H1 | H1].
assumption. false_hyp H1 H.
Qed.

Theorem NZlt_dec : forall n m : NZ, n < m \/ ~ n < m.
Proof.
intros n m; destruct (NZle_lt_dec m n);
[right; now apply -> NZle_nlt | now left].
Qed.

Theorem NZlt_dne : forall n m, ~ ~ n < m <-> n < m.
Proof.
intros n m; split; intro H;
[destruct (NZlt_dec n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
intro H1; false_hyp H H1].
Qed.

Theorem NZnle_lt : forall n m : NZ, ~ n <= m <-> m < n.
Proof.
intros n m. rewrite NZle_nlt. apply NZlt_dne.
Qed.

Theorem NZle_dec : forall n m : NZ, n <= m \/ ~ n <= m.
Proof.
intros n m; destruct (NZle_lt_dec n m);
[now left | right; now apply <- NZnle_lt].
Qed.

Theorem NZle_dne : forall n m : NZ, ~ ~ n <= m <-> n <= m.
Proof.
intros n m; split; intro H;
[destruct (NZle_dec n m) as [H1 | H1]; [assumption | false_hyp H1 H] |
intro H1; false_hyp H H1].
Qed.

Theorem NZlt__nlt_succ : forall n m : NZ, n < m <-> ~ m < S n.
Proof.
intros n m; rewrite NZlt_succ__le; symmetry; apply NZnle_lt.
Qed.

(** Stronger variant of induction with assumptions n >= 0 (n <= 0)
in the induction step *)

Section Induction.

Variable A : Z -> Prop.
Hypothesis Q_wd : predicate_wd NZE A.

Add Morphism A with signature NZE ==> iff as Q_morph.
Proof Q_wd.

Section Center.

Variable z : Z. (* A z is the basis of induction *)

Section RightInduction.

Let Q' := fun n : Z => forall m : NZ, z <= m -> m < n -> A m.

Add Morphism Q' with signature NZE ==> iff as Q'_pos_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem NZright_induction :
  A z -> (forall n : NZ, z <= n -> A n -> A (S n)) -> forall n : NZ, z <= n -> A n.
Proof.
intros Qz QS k k_ge_z.
assert (H : forall n : NZ, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3.
rewrite NZlt_succ in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_succ_pred m.
apply QS. now apply -> lt_n_m_pred. apply IH. now apply -> lt_n_m_pred.
rewrite H3; apply NZlt_pred_l. now rewrite <- H2.
intros n IH m H2 H3. apply IH. assumption. now apply lt_n_predm.
pose proof (H (S k)) as H1; unfold Q' in H1. apply H1.
apply k_ge_z. apply NZlt_succ_r.
Qed.

End RightInduction.

Section LeftInduction.

Let Q' := fun n : Z => forall m : NZ, m <= z -> n < m -> A m.

Add Morphism Q' with signature NZE ==> iff as Q'_neg_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem NZleft_induction :
  A z -> (forall n : NZ, n <= z -> A n -> A (P n)) -> forall n : NZ, n <= z -> A n.
Proof.
intros Qz QP k k_le_z.
assert (H : forall n : NZ, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3. apply IH. assumption. now apply lt_succ__lt.
intros n IH m H2 H3.
rewrite NZlt_pred in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_pred_succ m.
apply QP. now apply -> lt_n_m_succ. apply IH. now apply -> lt_n_m_succ.
rewrite H3; apply NZlt_succ_r. now rewrite H2.
pose proof (H (P k)) as H1; unfold Q' in H1. apply H1.
apply k_le_z. apply NZlt_pred_l.
Qed.

End LeftInduction.

Theorem NZinduction_ord_n :
  A z ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
  (forall n : NZ, n <= z -> A n -> A (P n)) ->
    forall n : NZ, A n.
Proof.
intros Qz QS QP n.
destruct (lt_total n z) as [H | [H | H]].
now apply left_induction; [| | Zle_intro1].
now rewrite H.
now apply right_induction; [| | Zle_intro1].
Qed.

End Center.

Theorem NZinduction_ord :
  A 0 ->
  (forall n : NZ, 0 <= n -> A n -> A (S n)) ->
  (forall n : NZ, n <= 0 -> A n -> A (P n)) ->
    forall n : NZ, A n.
Proof (induction_ord_n 0).

Theorem NZlt_ind : forall (n : Z),
  A (S n) ->
  (forall m : Z, n < m -> A m -> A (S m)) ->
   forall m : Z, n < m -> A m.
Proof.
intros n H1 H2 m H3.
apply right_induction with (S n). assumption.
intros; apply H2; try assumption. now apply <- lt_n_m_succ.
now apply -> lt_n_m_succ.
Qed.

Theorem NZle_ind : forall (n : Z),
  A n ->
  (forall m : Z, n <= m -> A m -> A (S m)) ->
   forall m : Z, n <= m -> A m.
Proof.
intros n H1 H2 m H3.
now apply right_induction with n.
Qed.

End Induction.

Ltac induct_ord n :=
  try intros until n;
  pattern n; apply induction_ord; clear n;
  [unfold NumPrelude.predicate_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | | |].

End ZOrderProperties.



(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
