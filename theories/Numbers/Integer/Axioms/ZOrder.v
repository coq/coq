Require Export ZAxioms.

Module Type ZOrderSignature.
Declare Module Export IntModule : IntSignature.
Open Local Scope IntScope.

Parameter Inline lt : Z -> Z -> bool.
Parameter Inline le : Z -> Z -> bool.
Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Add Morphism le with signature E ==> E ==> eq_bool as le_wd.

Notation "n <  m" := (lt n m) : IntScope.
Notation "n <= m" := (le n m) : IntScope.

Axiom le_lt : forall n m, n <= m <-> n < m \/ n == m.
Axiom lt_irr : forall n, ~ (n < n).
Axiom lt_S : forall n m, n < (S m) <-> n <= m.

End ZOrderSignature.


Module ZOrderProperties (Import ZOrderModule : ZOrderSignature).
Module Export IntPropertiesModule := IntProperties IntModule.
Open Local Scope IntScope.

Ltac Zle_intro1 := rewrite le_lt; left.
Ltac Zle_intro2 := rewrite le_lt; right.
Ltac Zle_elim H := rewrite le_lt in H; destruct H as [H | H].

Theorem le_refl : forall n, n <= n.
Proof.
intro n; now Zle_intro2.
Qed.

Theorem lt_n_Sn : forall n, n < S n.
Proof.
intro n. rewrite lt_S. now Zle_intro2.
Qed.

Theorem le_n_Sn : forall n, n <= S n.
Proof.
intro; Zle_intro1; apply lt_n_Sn.
Qed.

Theorem lt_Pn_n : forall n, P n < n.
Proof.
intro n; rewrite_S_P n at 2; apply lt_n_Sn.
Qed.

Theorem le_Pn_n : forall n, P n <= n.
Proof.
intro; Zle_intro1; apply lt_Pn_n.
Qed.

Theorem lt_n_Sm : forall n m, n < m -> n < S m.
Proof.
intros. rewrite lt_S. now Zle_intro1.
Qed.

Theorem le_n_Sm : forall n m, n <= m -> n <= S m.
Proof.
intros n m H; rewrite <- lt_S in H; now Zle_intro1.
Qed.

Theorem lt_n_m_P : forall n m, n < m <-> n <= P m.
Proof.
intros n m; rewrite_S_P m; rewrite P_S; apply lt_S.
Qed.

Theorem not_le_n_Pn : forall n, ~ n <= P n.
Proof.
intros n H; Zle_elim H.
apply lt_n_Sm in H; rewrite S_P in H; false_hyp H lt_irr.
pose proof (lt_Pn_n n) as H1; rewrite <- H in H1; false_hyp H1 lt_irr.
Qed.

Theorem le_S : forall n m, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite le_lt. now rewrite lt_S.
Qed.

Theorem lt_P : forall n m, (P n) < m <-> n <= m.
Proof.
intro n; induct_n m (P n).
split; intro H. false_hyp H lt_irr. false_hyp H not_le_n_Pn.
intros m IH; split; intro H.
apply -> lt_S in H; Zle_elim H.
apply -> IH in H; now apply le_n_Sm.
rewrite <- H; rewrite S_P; now Zle_intro2.
apply -> le_S in H; destruct H as [H | H].
apply <- IH in H. now apply lt_n_Sm. rewrite H; rewrite P_S; apply lt_n_Sn.
intros m IH; split; intro H.
pose proof H as H1. apply lt_n_Sm in H; rewrite S_P in H.
apply -> IH in H; Zle_elim H. now apply -> lt_n_m_P.
rewrite H in H1; false_hyp H1 lt_irr.
pose proof H as H1. apply le_n_Sm in H. rewrite S_P in H.
apply <- IH in H. apply -> lt_n_m_P in H. Zle_elim H.
assumption. apply P_inj in H; rewrite H in H1; false_hyp H1 not_le_n_Pn.
Qed.

Theorem lt_Pn_m : forall n m, n < m -> P n < m.
Proof.
intros; rewrite lt_P; now Zle_intro1.
Qed.

Theorem le_Pn_m : forall n m, n <= m -> P n <= m.
Proof.
intros n m H; rewrite <- lt_P in H; now Zle_intro1.
Qed.

Theorem lt_n_m_S : forall n m, n < m <-> S n <= m.
Proof.
intros n m; rewrite_P_S n; rewrite S_P; apply lt_P.
Qed.

Theorem lt_Sn_m : forall n m, S n < m -> n < m.
Proof.
intros n m H; rewrite_P_S n; now apply lt_Pn_m.
Qed.

Theorem le_Sn_m : forall n m, S n <= m -> n <= m.
Proof.
intros n m H; rewrite <- lt_n_m_S in H; now Zle_intro1.
Qed.

Theorem lt_n_Pm : forall n m, n < P m -> n < m.
Proof.
intros n m H; rewrite_S_P m; now apply lt_n_Sm.
Qed.

Theorem le_n_Pm : forall n m, n <= P m -> n <= m.
Proof.
intros n m H; rewrite <- lt_n_m_P in H; now Zle_intro1.
Qed.

Theorem lt_respects_S : forall n m, n < m <-> S n < S m.
Proof.
intros n m. rewrite lt_n_m_S. symmetry. apply lt_S.
Qed.

Theorem le_respects_S : forall n m, n <= m <-> S n <= S m.
Proof.
intros n m. do 2 rewrite le_lt.
firstorder using lt_respects_S S_wd S_inj.
Qed.

Theorem lt_respects_P : forall n m, n < m <-> P n < P m.
Proof.
intros n m. rewrite lt_n_m_P. symmetry; apply lt_P.
Qed.

Theorem le_respects_P : forall n m, n <= m <-> P n <= P m.
Proof.
intros n m. do 2 rewrite le_lt.
firstorder using lt_respects_P P_wd P_inj.
Qed.

Theorem lt_S_P : forall n m, S n < m <-> n < P m.
Proof.
intros n m; rewrite_P_S n at 2; apply lt_respects_P.
Qed.

Theorem le_S_P : forall n m, S n <= m <-> n <= P m.
Proof.
intros n m; rewrite_P_S n at 2; apply le_respects_P.
Qed.

Theorem lt_P_S : forall n m, P n < m <-> n < S m.
Proof.
intros n m; rewrite_S_P n at 2; apply lt_respects_S.
Qed.

Theorem le_P_S : forall n m, P n <= m <-> n <= S m.
Proof.
intros n m; rewrite_S_P n at 2; apply le_respects_S.
Qed.

Theorem lt_neq : forall n m, n < m -> n # m.
Proof.
intros n m H1 H2; rewrite H2 in H1; false_hyp H1 lt_irr.
Qed.

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof.
intros n m; induct_n n m.
intros p H _; false_hyp H lt_irr.
intros n IH p H1 H2. apply lt_Sn_m in H1. pose proof (IH p H1 H2) as H3.
rewrite lt_n_m_S in H3; Zle_elim H3.
assumption. rewrite <- H3 in H2. rewrite lt_S in H2; Zle_elim H2.
elimtype False; apply lt_irr with (n := n); now apply IH.
rewrite H2 in H1; false_hyp H1 lt_irr.
intros n IH p H1 H2. apply lt_Pn_m. rewrite lt_P in H1; Zle_elim H1.
now apply IH. now rewrite H1.
Qed.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
intros n m p H1 H2; Zle_elim H1.
Zle_elim H2. Zle_intro1; now apply lt_trans with (m := m).
Zle_intro1; now rewrite <- H2. now rewrite H1.
Qed.

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof.
intros n m p H1 H2; Zle_elim H1.
now apply lt_trans with (m := m). now rewrite H1.
Qed.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof.
intros n m p H1 H2; Zle_elim H2.
now apply lt_trans with (m := m). now rewrite <- H2.
Qed.

Theorem lt_asymm : forall n m, n < m -> ~ m < n.
Proof.
intros n m H1 H2; apply lt_irr with (n := n); now apply lt_trans with (m := m).
Qed.

Theorem le_antisym : forall n m, n <= m -> m <= n -> n == m.
Proof.
intros n m H1 H2; Zle_elim H1; Zle_elim H2.
elimtype False; apply lt_irr with (n := n); now apply lt_trans with (m := m).
now symmetry. assumption. assumption.
Qed.

Theorem not_lt_Sn_n : forall n, ~ S n < n.
Proof.
intros n H; apply (lt_asymm n (S n)). apply lt_n_Sn. assumption.
Qed.

Theorem not_le_Sn_n : forall n, ~ S n <= n.
Proof.
intros n H; Zle_elim H. false_hyp H not_lt_Sn_n.
pose proof (lt_n_Sn n) as H1. rewrite H in H1; false_hyp H1 lt_irr.
Qed.

Theorem lt_gt : forall n m, n < m -> m < n -> False.
Proof.
intros n m H1 H2; apply lt_irr with (n := n); now apply lt_trans with (m := m).
Qed.

Theorem lt_total : forall n m,  n < m \/ n == m \/ m < n.
Proof.
intros n m; induct_n n m.
right; now left.
intros n IH; destruct IH as [H | [H | H]].
rewrite lt_n_m_S in H. rewrite le_lt in H; tauto.
right; right; rewrite H; apply lt_n_Sn.
right; right; now apply lt_n_Sm.
intros n IH; destruct IH as [H | [H | H]].
left; now apply lt_Pn_m.
left; rewrite H; apply lt_Pn_n.
rewrite lt_n_m_P in H. rewrite le_lt in H.
setoid_replace (m == P n) with (P n == m) in H using relation iff. tauto.
split; intro; now symmetry.
Qed.

Theorem le_gt : forall n m, n <= m <-> ~ m < n.
Proof.
intros n m. rewrite -> le_lt.
pose proof (lt_total n m). pose proof (lt_gt n m).
assert (n == m -> ~ m < n); [intro A; rewrite A; apply lt_irr |].
tauto.
Qed.

Theorem lt_ge : forall n m, n < m <-> ~ m <= n.
Proof.
intros n m. rewrite -> le_lt.
pose proof (lt_total m n). pose proof (lt_gt n m).
assert (n < m -> m # n); [intros A B; rewrite B in A; false_hyp A lt_irr |].
tauto.
Qed.

Theorem lt_discrete : forall n m, n < m -> m < S n -> False.
Proof.
intros n m H1 H2; apply -> lt_S in H2; apply -> lt_ge in H1; false_hyp H2 H1.
Qed.

(* Decidability of order can be proved either from totality or from the fact
that < and <= are boolean functions *)

(** A corollary of having an order is that Z is infinite in both
directions *)

Theorem neq_Sn_n : forall n, S n # n.
Proof.
intros n H. pose proof (lt_n_Sn n) as H1. rewrite H in H1. false_hyp H1 lt_irr.
Qed.

Theorem neq_Pn_n : forall n, P n # n.
Proof.
intros n H. apply S_wd in H. rewrite S_P in H. now apply neq_Sn_n with (n := n).
Qed.

Definition nth_S (n : nat) (m : Z) :=
  nat_rec (fun _ => Z) m (fun _ l => S l) n.
Definition nth_P (n : nat) (m : Z) :=
  nat_rec (fun _ => Z) m (fun _ l => P l) n.

Lemma lt_m_Skm :
  forall (n : nat) (m : Z), m < nth_S (Datatypes.S n) m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply lt_n_Sn. now apply lt_n_Sm.
Qed.

Lemma lt_Pkm_m :
  forall (n : nat) (m : Z), nth_P (Datatypes.S n) m < m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply lt_Pn_n. now apply lt_Pn_m.
Qed.

Theorem neq_m_Skm :
  forall (n : nat) (m : Z), nth_S (Datatypes.S n) m # m.
Proof.
intros n m H. pose proof (lt_m_Skm n m) as H1. rewrite H in H1.
false_hyp H1 lt_irr.
Qed.

Theorem neq_Pkm_m :
  forall (n : nat) (m : Z), nth_P (Datatypes.S n) m # m.
Proof.
intros n m H. pose proof (lt_Pkm_m n m) as H1. rewrite H in H1.
false_hyp H1 lt_irr.
Qed.

(** Stronger variant of induction with assumptions n >= 0 (n <= 0)
in the induction step *)

Section Induction.

Variable Q : Z -> Prop.
Hypothesis Q_wd : pred_wd E Q.

Add Morphism Q with signature E ==> iff as Q_morph.
Proof Q_wd.

Section Center.

Variable z : Z. (* Q z is the basis of induction *)

Section RightInduction.

Let Q' := fun n : Z => forall m, z <= m -> m < n -> Q m.

Add Morphism Q' with signature E ==> iff as Q'_pos_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem right_induction :
  Q z -> (forall n, z <= n -> Q n -> Q (S n)) -> forall n, z <= n -> Q n.
Proof.
intros Qz QS k k_ge_z.
assert (H : forall n, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3.
rewrite lt_S in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_S_P m.
apply QS. now apply -> lt_n_m_P. apply IH. now apply -> lt_n_m_P.
rewrite H3; apply lt_Pn_n. now rewrite <- H2.
intros n IH m H2 H3. apply IH. assumption. now apply lt_n_Pm.
pose proof (H (S k)) as H1; unfold Q' in H1. apply H1.
apply k_ge_z. apply lt_n_Sn.
Qed.

End RightInduction.

Section LeftInduction.

Let Q' := fun n : Z => forall m, m <= z -> n < m -> Q m.

Add Morphism Q' with signature E ==> iff as Q'_neg_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem left_induction :
  Q z -> (forall n, n <= z -> Q n -> Q (P n)) -> forall n, n <= z -> Q n.
Proof.
intros Qz QP k k_le_z.
assert (H : forall n, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3. apply IH. assumption. now apply lt_Sn_m.
intros n IH m H2 H3.
rewrite lt_P in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_P_S m.
apply QP. now apply -> lt_n_m_S. apply IH. now apply -> lt_n_m_S.
rewrite H3; apply lt_n_Sn. now rewrite H2.
pose proof (H (P k)) as H1; unfold Q' in H1. apply H1.
apply k_le_z. apply lt_Pn_n.
Qed.

End LeftInduction.

Theorem induction_ord_n :
  Q z ->
  (forall n, z <= n -> Q n -> Q (S n)) ->
  (forall n, n <= z -> Q n -> Q (P n)) ->
    forall n, Q n.
Proof.
intros Qz QS QP n.
destruct (lt_total n z) as [H | [H | H]].
now apply left_induction; [| | Zle_intro1].
now rewrite H.
now apply right_induction; [| | Zle_intro1].
Qed.

End Center.

Theorem induction_ord :
  Q 0 ->
  (forall n, 0 <= n -> Q n -> Q (S n)) ->
  (forall n, n <= 0 -> Q n -> Q (P n)) ->
    forall n, Q n.
Proof (induction_ord_n 0).

Theorem lt_ind : forall (n : Z),
  Q (S n) ->
  (forall m : Z, n < m -> Q m -> Q (S m)) ->
   forall m : Z, n < m -> Q m.
Proof.
intros n H1 H2 m H3.
apply right_induction with (S n). assumption.
intros; apply H2; try assumption. now apply <- lt_n_m_S.
now apply -> lt_n_m_S.
Qed.

Theorem le_ind : forall (n : Z),
  Q n ->
  (forall m : Z, n <= m -> Q m -> Q (S m)) ->
   forall m : Z, n <= m -> Q m.
Proof.
intros n H1 H2 m H3.
now apply right_induction with n.
Qed.

End Induction.

Ltac induct_ord n :=
  try intros until n;
  pattern n; apply induction_ord; clear n;
  [unfold NumPrelude.pred_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | | |].

End ZOrderProperties.

