Require Export NAxioms.

Module Type PlusSignature.
Declare Module Export NatModule : NatSignature.

Parameter Inline plus : N -> N -> N.

Notation "x + y" := (plus x y).

Add Morphism plus with signature E ==> E ==> E as plus_wd.

Axiom plus_0_n : forall n, 0 + n == n.
Axiom plus_Sn_m : forall n m, (S n) + m == S (n + m).

End PlusSignature.

Module PlusProperties (Export PlusModule : PlusSignature).

Module Export NatPropertiesModule := NatProperties NatModule.

Lemma plus_0_r : forall n, n + 0 == n.
Proof.
induct n.
now rewrite plus_0_n.
intros x IH.
rewrite plus_Sn_m.
now rewrite IH.
Qed.

Lemma plus_0_l : forall n, 0 + n == n.
Proof.
intro n.
now rewrite plus_0_n.
Qed.

Lemma plus_n_Sm : forall n m, n + S m == S (n + m).
Proof.
intros n m; generalize n; clear n. induct n.
now repeat rewrite plus_0_n.
intros x IH.
repeat rewrite plus_Sn_m; now rewrite IH.
Qed.

Lemma plus_Sn_m : forall n m, S n + m == S (n + m).
Proof.
intros.
now rewrite plus_Sn_m.
Qed.

Lemma plus_comm : forall n m, n + m == m + n.
Proof.
intros n m; generalize n; clear n. induct n.
rewrite plus_0_l; now rewrite plus_0_r.
intros x IH.
rewrite plus_Sn_m; rewrite plus_n_Sm; now rewrite IH.
Qed.

Lemma plus_assoc : forall n m p, n + (m + p) == (n + m) + p.
Proof.
intros n m p; generalize n; clear n. induct n.
now repeat rewrite plus_0_l.
intros x IH.
repeat rewrite plus_Sn_m; now rewrite IH.
Qed.

Lemma plus_1_l : forall n, 1 + n == S n.
Proof.
intro n; rewrite plus_Sn_m; now rewrite plus_0_n.
Qed.

Lemma plus_1_r : forall n, n + 1 == S n.
Proof.
intro n; rewrite plus_comm; apply plus_1_l.
Qed.

Lemma plus_cancel_l : forall n m p, p + n == p + m -> n == m.
Proof.
induct p.
do 2 rewrite plus_0_n; trivial.
intros p IH H. do 2 rewrite plus_Sn_m in H. apply S_inj in H. now apply IH.
Qed.

Lemma plus_cancel_r : forall n m p, n + p == m + p -> n == m.
Proof.
intros n m p.
rewrite plus_comm.
set (k := p + n); rewrite plus_comm; unfold k.
apply plus_cancel_l.
Qed.

Lemma plus_eq_0 : forall n m, n + m == 0 -> n == 0 /\ m == 0.
Proof.
intros n m; induct n.
rewrite plus_0_n; now split.
intros n IH H. rewrite plus_Sn_m in H.
absurd_hyp H; [|assumption]. unfold not; apply S_0.
Qed.

Lemma succ_plus_discr : forall n m, m # S (n + m).
Proof.
intro n; induct m.
intro H. apply S_0 with (n := (n + 0)). now apply (proj2 (proj2 E_equiv)). (* symmetry *)
intros m IH H. apply S_inj in H. rewrite plus_n_Sm in H.
unfold not in IH; now apply IH.
Qed.

Lemma n_SSn : forall n, n # S (S n).
Proof.
intro n. pose proof (succ_plus_discr 1 n) as H.
rewrite plus_Sn_m in H; now rewrite plus_0_n in H.
Qed.

Lemma n_SSSn : forall n, n # S (S (S n)).
Proof.
intro n. pose proof (succ_plus_discr (S (S 0)) n) as H.
do 2 rewrite plus_Sn_m in H. now rewrite plus_0_n in H.
Qed.

Lemma n_SSSSn : forall n, n # S (S (S (S n))).
Proof.
intro n. pose proof (succ_plus_discr (S (S (S 0))) n) as H.
do 3 rewrite plus_Sn_m in H. now rewrite plus_0_n in H.
Qed.

(* The following section is devoted to defining a function that, given
two numbers whose some equals 1, decides which number equals 1. The
main property of the function is also proved .*)

(* First prove a theorem with ordinary disjunction *)
Theorem plus_eq_1 :
  forall m n, m + n == 1 ->  (m == 0 /\ n == 1) \/ (m == 1 /\ n == 0).
induct m.
intros n H; rewrite plus_0_n in H; left; now split.
intros n IH m H; rewrite plus_Sn_m in H; apply S_inj in H;
apply plus_eq_0 in H; destruct H as [H1 H2];
now right; split; [apply S_wd |].
Qed.

Definition plus_eq_1_dec (m n : N) : bool := recursion true (fun _ _ => false) m.

Lemma plus_eq_1_dec_step_wd : fun2_wd E eq_bool eq_bool (fun _ _ => false).
Proof.
unfold fun2_wd; intros. unfold eq_bool. reflexivity.
Qed.

Add Morphism plus_eq_1_dec with signature E ==> E ==> eq_bool as plus_eq_1_dec_wd.
Proof.
unfold fun2_wd, plus_eq_1_dec.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
unfold eq_bool; reflexivity.
unfold eq_fun2; unfold eq_bool; reflexivity.
assumption.
Qed.

Lemma plus_eq_1_dec_0 : forall n, plus_eq_1_dec 0 n = true.
Proof.
intro n. unfold plus_eq_1_dec.
now apply recursion_0.
Qed.

Lemma plus_eq_1_dec_S : forall m n, plus_eq_1_dec (S n) m = false.
Proof.
intros n m. unfold plus_eq_1_dec.
now rewrite (recursion_S eq_bool);
[| unfold eq_bool | apply plus_eq_1_dec_step_wd].
Qed.

Theorem plus_eq_1_dec_correct :
  forall m n, m + n == 1 ->
    (plus_eq_1_dec m n = true  -> m == 0 /\ n == 1) /\
    (plus_eq_1_dec m n = false -> m == 1 /\ n == 0).
Proof.
intros m n; induct m.
intro H. rewrite plus_0_l in H.
rewrite plus_eq_1_dec_0.
split; [intros; now split | intro H1; discriminate H1].
intros m _ H. rewrite plus_eq_1_dec_S.
split; [intro H1; discriminate | intros _ ].
rewrite plus_Sn_m in H. apply S_inj in H.
apply plus_eq_0 in H; split; [apply S_wd | ]; tauto.
Qed.

End PlusProperties.
