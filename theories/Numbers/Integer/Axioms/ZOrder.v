Require Export ZAxioms.

Module Type ZOrderSignature.
Declare Module Export ZBaseMod : ZBaseSig.
Open Local Scope IntScope.

Parameter Inline lt : Z -> Z -> bool.
Parameter Inline le : Z -> Z -> bool.
Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Add Morphism le with signature E ==> E ==> eq_bool as le_wd.

Notation "n <  m" := (lt n m) : IntScope.
Notation "n <= m" := (le n m) : IntScope.

Axiom le_lt : forall n m, n <= m <-> n < m \/ n == m.
Axiom lt_irr : forall n, ~ (n < n).
Axiom lt_succ : forall n m, n < (S m) <-> n <= m.

End ZOrderSignature.


Module ZOrderProperties (Import ZOrderModule : ZOrderSignature).
Module Export ZBasePropFunctModule := ZBasePropFunct ZBaseMod.
Open Local Scope IntScope.

Ltac Zle_intro1 := rewrite le_lt; left.
Ltac Zle_intro2 := rewrite le_lt; right.
Ltac Zle_elim H := rewrite le_lt in H; destruct H as [H | H].

Theorem le_refl : forall n, n <= n.
Proof.
intro n; now Zle_intro2.
Qed.

Theorem lt_n_succn : forall n, n < S n.
Proof.
intro n. rewrite lt_succ. now Zle_intro2.
Qed.

Theorem le_n_succn : forall n, n <= S n.
Proof.
intro; Zle_intro1; apply lt_n_succn.
Qed.

Theorem lt_predn_n : forall n, P n < n.
Proof.
intro n; rewrite_succ_pred n at 2; apply lt_n_succn.
Qed.

Theorem le_predn_n : forall n, P n <= n.
Proof.
intro; Zle_intro1; apply lt_predn_n.
Qed.

Theorem lt_n_succm : forall n m, n < m -> n < S m.
Proof.
intros. rewrite lt_succ. now Zle_intro1.
Qed.

Theorem le_n_succm : forall n m, n <= m -> n <= S m.
Proof.
intros n m H; rewrite <- lt_succ in H; now Zle_intro1.
Qed.

Theorem lt_n_m_pred : forall n m, n < m <-> n <= P m.
Proof.
intros n m; rewrite_succ_pred m; rewrite pred_succ; apply lt_succ.
Qed.

Theorem not_le_n_predn : forall n, ~ n <= P n.
Proof.
intros n H; Zle_elim H.
apply lt_n_succm in H; rewrite succ_pred in H; false_hyp H lt_irr.
pose proof (lt_predn_n n) as H1; rewrite <- H in H1; false_hyp H1 lt_irr.
Qed.

Theorem le_succ : forall n m, n <= S m <-> n <= m \/ n == S m.
Proof.
intros n m; rewrite le_lt. now rewrite lt_succ.
Qed.

Theorem lt_pred : forall n m, (P n) < m <-> n <= m.
Proof.
intro n; induct_n m (P n).
split; intro H. false_hyp H lt_irr. false_hyp H not_le_n_predn.
intros m IH; split; intro H.
apply -> lt_succ in H; Zle_elim H.
apply -> IH in H; now apply le_n_succm.
rewrite <- H; rewrite succ_pred; now Zle_intro2.
apply -> le_succ in H; destruct H as [H | H].
apply <- IH in H. now apply lt_n_succm. rewrite H; rewrite pred_succ; apply lt_n_succn.
intros m IH; split; intro H.
pose proof H as H1. apply lt_n_succm in H; rewrite succ_pred in H.
apply -> IH in H; Zle_elim H. now apply -> lt_n_m_pred.
rewrite H in H1; false_hyp H1 lt_irr.
pose proof H as H1. apply le_n_succm in H. rewrite succ_pred in H.
apply <- IH in H. apply -> lt_n_m_pred in H. Zle_elim H.
assumption. apply pred_inj in H; rewrite H in H1; false_hyp H1 not_le_n_predn.
Qed.

Theorem lt_predn_m : forall n m, n < m -> P n < m.
Proof.
intros; rewrite lt_pred; now Zle_intro1.
Qed.

Theorem le_predn_m : forall n m, n <= m -> P n <= m.
Proof.
intros n m H; rewrite <- lt_pred in H; now Zle_intro1.
Qed.

Theorem lt_n_m_succ : forall n m, n < m <-> S n <= m.
Proof.
intros n m; rewrite_pred_succ n; rewrite succ_pred; apply lt_pred.
Qed.

Theorem lt_succn_m : forall n m, S n < m -> n < m.
Proof.
intros n m H; rewrite_pred_succ n; now apply lt_predn_m.
Qed.

Theorem le_succn_m : forall n m, S n <= m -> n <= m.
Proof.
intros n m H; rewrite <- lt_n_m_succ in H; now Zle_intro1.
Qed.

Theorem lt_n_predm : forall n m, n < P m -> n < m.
Proof.
intros n m H; rewrite_succ_pred m; now apply lt_n_succm.
Qed.

Theorem le_n_predm : forall n m, n <= P m -> n <= m.
Proof.
intros n m H; rewrite <- lt_n_m_pred in H; now Zle_intro1.
Qed.

Theorem lt_respects_succ : forall n m, n < m <-> S n < S m.
Proof.
intros n m. rewrite lt_n_m_succ. symmetry. apply lt_succ.
Qed.

Theorem le_respects_succ : forall n m, n <= m <-> S n <= S m.
Proof.
intros n m. do 2 rewrite le_lt.
firstorder using lt_respects_succ succ_wd succ_inj.
Qed.

Theorem lt_respects_pred : forall n m, n < m <-> P n < P m.
Proof.
intros n m. rewrite lt_n_m_pred. symmetry; apply lt_pred.
Qed.

Theorem le_respects_pred : forall n m, n <= m <-> P n <= P m.
Proof.
intros n m. do 2 rewrite le_lt.
firstorder using lt_respects_pred pred_wd pred_inj.
Qed.

Theorem lt_succ_pred : forall n m, S n < m <-> n < P m.
Proof.
intros n m; rewrite_pred_succ n at 2; apply lt_respects_pred.
Qed.

Theorem le_succ_pred : forall n m, S n <= m <-> n <= P m.
Proof.
intros n m; rewrite_pred_succ n at 2; apply le_respects_pred.
Qed.

Theorem lt_pred_succ : forall n m, P n < m <-> n < S m.
Proof.
intros n m; rewrite_succ_pred n at 2; apply lt_respects_succ.
Qed.

Theorem le_pred_succ : forall n m, P n <= m <-> n <= S m.
Proof.
intros n m; rewrite_succ_pred n at 2; apply le_respects_succ.
Qed.

Theorem lt_neq : forall n m, n < m -> n # m.
Proof.
intros n m H1 H2; rewrite H2 in H1; false_hyp H1 lt_irr.
Qed.

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof.
intros n m; induct_n n m.
intros p H _; false_hyp H lt_irr.
intros n IH p H1 H2. apply lt_succn_m in H1. pose proof (IH p H1 H2) as H3.
rewrite lt_n_m_succ in H3; Zle_elim H3.
assumption. rewrite <- H3 in H2. rewrite lt_succ in H2; Zle_elim H2.
elimtype False; apply lt_irr with (n := n); now apply IH.
rewrite H2 in H1; false_hyp H1 lt_irr.
intros n IH p H1 H2. apply lt_predn_m. rewrite lt_pred in H1; Zle_elim H1.
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

Theorem not_lt_succn_n : forall n, ~ S n < n.
Proof.
intros n H; apply (lt_asymm n (S n)). apply lt_n_succn. assumption.
Qed.

Theorem not_le_succn_n : forall n, ~ S n <= n.
Proof.
intros n H; Zle_elim H. false_hyp H not_lt_succn_n.
pose proof (lt_n_succn n) as H1. rewrite H in H1; false_hyp H1 lt_irr.
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
rewrite lt_n_m_succ in H. rewrite le_lt in H; tauto.
right; right; rewrite H; apply lt_n_succn.
right; right; now apply lt_n_succm.
intros n IH; destruct IH as [H | [H | H]].
left; now apply lt_predn_m.
left; rewrite H; apply lt_predn_n.
rewrite lt_n_m_pred in H. rewrite le_lt in H.
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
intros n m H1 H2; apply -> lt_succ in H2; apply -> lt_ge in H1; false_hyp H2 H1.
Qed.

(* Decidability of order can be proved either from totality or from the fact
that < and <= are boolean functions *)

(** A corollary of having an order is that Z is infinite in both
directions *)

Theorem neq_succn_n : forall n, S n # n.
Proof.
intros n H. pose proof (lt_n_succn n) as H1. rewrite H in H1. false_hyp H1 lt_irr.
Qed.

Theorem neq_predn_n : forall n, P n # n.
Proof.
intros n H. apply succ_wd in H. rewrite succ_pred in H. now apply neq_succn_n with (n := n).
Qed.

Definition nth_succ (n : nat) (m : Z) :=
  nat_rec (fun _ => Z) m (fun _ l => S l) n.
Definition nth_pred (n : nat) (m : Z) :=
  nat_rec (fun _ => Z) m (fun _ l => P l) n.

Lemma lt_m_succkm :
  forall (n : nat) (m : Z), m < nth_succ (Datatypes.S n) m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply lt_n_succn. now apply lt_n_succm.
Qed.

Lemma lt_predkm_m :
  forall (n : nat) (m : Z), nth_pred (Datatypes.S n) m < m.
Proof.
intros n m; induction n as [| n IH]; simpl in *.
apply lt_predn_n. now apply lt_predn_m.
Qed.

Theorem neq_m_succkm :
  forall (n : nat) (m : Z), nth_succ (Datatypes.S n) m # m.
Proof.
intros n m H. pose proof (lt_m_succkm n m) as H1. rewrite H in H1.
false_hyp H1 lt_irr.
Qed.

Theorem neq_predkm_m :
  forall (n : nat) (m : Z), nth_pred (Datatypes.S n) m # m.
Proof.
intros n m H. pose proof (lt_predkm_m n m) as H1. rewrite H in H1.
false_hyp H1 lt_irr.
Qed.

(** Stronger variant of induction with assumptions n >= 0 (n <= 0)
in the induction step *)

Section Induction.

Variable A : Z -> Prop.
Hypothesis Q_wd : predicate_wd E A.

Add Morphism A with signature E ==> iff as Q_morph.
Proof Q_wd.

Section Center.

Variable z : Z. (* A z is the basis of induction *)

Section RightInduction.

Let Q' := fun n : Z => forall m, z <= m -> m < n -> A m.

Add Morphism Q' with signature E ==> iff as Q'_pos_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem right_induction :
  A z -> (forall n, z <= n -> A n -> A (S n)) -> forall n, z <= n -> A n.
Proof.
intros Qz QS k k_ge_z.
assert (H : forall n, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3.
rewrite lt_succ in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_succ_pred m.
apply QS. now apply -> lt_n_m_pred. apply IH. now apply -> lt_n_m_pred.
rewrite H3; apply lt_predn_n. now rewrite <- H2.
intros n IH m H2 H3. apply IH. assumption. now apply lt_n_predm.
pose proof (H (S k)) as H1; unfold Q' in H1. apply H1.
apply k_ge_z. apply lt_n_succn.
Qed.

End RightInduction.

Section LeftInduction.

Let Q' := fun n : Z => forall m, m <= z -> n < m -> A m.

Add Morphism Q' with signature E ==> iff as Q'_neg_wd.
Proof.
intros x1 x2 H; unfold Q'; qmorphism x1 x2.
Qed.

Theorem left_induction :
  A z -> (forall n, n <= z -> A n -> A (P n)) -> forall n, n <= z -> A n.
Proof.
intros Qz QP k k_le_z.
assert (H : forall n, Q' n). induct_n n z; unfold Q'.
intros m H1 H2. apply -> le_gt in H1; false_hyp H2 H1.
intros n IH m H2 H3. apply IH. assumption. now apply lt_succn_m.
intros n IH m H2 H3.
rewrite lt_pred in H3; Zle_elim H3. now apply IH.
Zle_elim H2. rewrite_pred_succ m.
apply QP. now apply -> lt_n_m_succ. apply IH. now apply -> lt_n_m_succ.
rewrite H3; apply lt_n_succn. now rewrite H2.
pose proof (H (P k)) as H1; unfold Q' in H1. apply H1.
apply k_le_z. apply lt_predn_n.
Qed.

End LeftInduction.

Theorem induction_ord_n :
  A z ->
  (forall n, z <= n -> A n -> A (S n)) ->
  (forall n, n <= z -> A n -> A (P n)) ->
    forall n, A n.
Proof.
intros Qz QS QP n.
destruct (lt_total n z) as [H | [H | H]].
now apply left_induction; [| | Zle_intro1].
now rewrite H.
now apply right_induction; [| | Zle_intro1].
Qed.

End Center.

Theorem induction_ord :
  A 0 ->
  (forall n, 0 <= n -> A n -> A (S n)) ->
  (forall n, n <= 0 -> A n -> A (P n)) ->
    forall n, A n.
Proof (induction_ord_n 0).

Theorem lt_ind : forall (n : Z),
  A (S n) ->
  (forall m : Z, n < m -> A m -> A (S m)) ->
   forall m : Z, n < m -> A m.
Proof.
intros n H1 H2 m H3.
apply right_induction with (S n). assumption.
intros; apply H2; try assumption. now apply <- lt_n_m_succ.
now apply -> lt_n_m_succ.
Qed.

Theorem le_ind : forall (n : Z),
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
