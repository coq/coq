(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Plus.
Require Export Minus.
Require Export Lt.
Require Export Le.

Open Local Scope nat_scope.

Implicit Types m n p : nat.

(** Theorems about multiplication in [nat]. [mult] is defined in module [Init/Peano.v]. *)

(** * [nat] is a semi-ring *)

(** ** Zero property *)

Lemma mult_0_r : forall n, n * 0 = 0.
Proof.
  intro; symmetry  in |- *; apply mult_n_O.
Qed.

Lemma mult_0_l : forall n, 0 * n = 0.
Proof.
  reflexivity.
Qed.

(** ** 1 is neutral *)

Lemma mult_1_l : forall n, 1 * n = n.
Proof.
  simpl in |- *; auto with arith.
Qed.
Hint Resolve mult_1_l: arith v62.

Lemma mult_1_r : forall n, n * 1 = n.
Proof.
  induction n; [ trivial | 
    simpl; rewrite IHn; reflexivity].
Qed.
Hint Resolve mult_1_r: arith v62.

(** ** Commutativity *)

Lemma mult_comm : forall n m, n * m = m * n.
Proof.
intros; elim n; intros; simpl in |- *; auto with arith.
elim mult_n_Sm.
elim H; apply plus_comm.
Qed.
Hint Resolve mult_comm: arith v62.

(** ** Distributivity *)

Lemma mult_plus_distr_r : forall n m p, (n + m) * p = n * p + m * p.
Proof.
  intros; elim n; simpl in |- *; intros; auto with arith.
  elim plus_assoc; elim H; auto with arith.
Qed.
Hint Resolve mult_plus_distr_r: arith v62.

Lemma mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
Proof.
  induction n. trivial.
  intros. simpl in |- *. rewrite (IHn m p). apply sym_eq. apply plus_permute_2_in_4.
Qed.

Lemma mult_minus_distr_r : forall n m p, (n - m) * p = n * p - m * p.
Proof.
  intros; pattern n, m in |- *; apply nat_double_ind; simpl in |- *; intros;
    auto with arith.
  elim minus_plus_simpl_l_reverse; auto with arith.
Qed.
Hint Resolve mult_minus_distr_r: arith v62.

Lemma mult_minus_distr_l : forall n m p, n * (m - p) = n * m - n * p.
Proof.
  intros n m p. rewrite mult_comm. rewrite mult_minus_distr_r. 
  rewrite (mult_comm m n); rewrite (mult_comm p n); reflexivity.
Qed.
Hint Resolve mult_minus_distr_l: arith v62.

(** ** Associativity *)

Lemma mult_assoc_reverse : forall n m p, n * m * p = n * (m * p).
Proof.
  intros; elim n; intros; simpl in |- *; auto with arith.
  rewrite mult_plus_distr_r.
  elim H; auto with arith.
Qed.
Hint Resolve mult_assoc_reverse: arith v62.

Lemma mult_assoc : forall n m p, n * (m * p) = n * m * p.
Proof.
  auto with arith.
Qed.
Hint Resolve mult_assoc: arith v62.

(** ** Inversion lemmas *)

Lemma mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  destruct n as [| n]. 
    intros; left; trivial.

    simpl; intros m H; right. 
    assert (H':m = 0 /\ n * m = 0) by apply (plus_is_O _ _ H).
    destruct H'; trivial.
Qed.

Lemma mult_is_one : forall n m, n * m = 1 -> n = 1 /\ m = 1.
Proof.
  destruct n as [|n].
    simpl; intros m H; elim (O_S _ H).

    simpl; intros m H.
    destruct (plus_is_one _ _ H) as [[Hm Hnm] | [Hm Hnm]].
      rewrite Hm in H; simpl in H; rewrite mult_0_r in H; elim (O_S _ H).
      rewrite Hm in Hnm; rewrite mult_1_r in Hnm; auto. 
Qed.

(** * Compatibility with orders *)

Lemma mult_O_le : forall n m, m = 0 \/ n <= m * n.
Proof.
  induction m; simpl in |- *; auto with arith.
Qed.
Hint Resolve mult_O_le: arith v62.

Lemma mult_le_compat_l : forall n m p, n <= m -> p * n <= p * m.
Proof.
  induction p as [| p IHp]. intros. simpl in |- *. apply le_n.
  intros. simpl in |- *. apply plus_le_compat. assumption.
  apply IHp. assumption.
Qed.
Hint Resolve mult_le_compat_l: arith.


Lemma mult_le_compat_r : forall n m p, n <= m -> n * p <= m * p.
Proof.
  intros m n p H.
  rewrite mult_comm. rewrite (mult_comm n).
  auto with arith.
Qed.

Lemma mult_le_compat :
  forall n m p (q:nat), n <= m -> p <= q -> n * p <= m * q.
Proof.
  intros m n p q Hmn Hpq; induction Hmn.
  induction Hpq.
  (* m*p<=m*p *)
  apply le_n.
  (* m*p<=m*m0 -> m*p<=m*(S m0) *)
  rewrite <- mult_n_Sm; apply le_trans with (m * m0).
  assumption.
  apply le_plus_l.
  (* m*p<=m0*q -> m*p<=(S m0)*q *)
  simpl in |- *; apply le_trans with (m0 * q).
  assumption.
  apply le_plus_r.
Qed.

Lemma mult_S_lt_compat_l : forall n m p, m < p -> S n * m < S n * p.
Proof.
  intro m; induction m. intros. simpl in |- *. rewrite <- plus_n_O. rewrite <- plus_n_O. assumption.
  intros. exact (plus_lt_compat _ _ _ _ H (IHm _ _ H)).
Qed.

Hint Resolve mult_S_lt_compat_l: arith.

Lemma mult_lt_compat_r : forall n m p, n < m -> 0 < p -> n * p < m * p.
Proof.
  intros m n p H H0.
  induction p.
  elim (lt_irrefl _ H0).
  rewrite mult_comm.
  replace (n * S p) with (S p * n); auto with arith.
Qed.

Lemma mult_S_le_reg_l : forall n m p, S n * m <= S n * p -> m <= p.
Proof.
  intros m n p H. elim (le_or_lt n p). trivial.
  intro H0. cut (S m * n < S m * n). intro. elim (lt_irrefl _ H1).
  apply le_lt_trans with (m := S m * p). assumption.
  apply mult_S_lt_compat_l. assumption.
Qed.

(** * n|->2*n and n|->2n+1 have disjoint image *)

Theorem odd_even_lem : forall p q, 2 * p + 1 <> 2 * q.
Proof.
  intros p; elim p; auto.
  intros q; case q; simpl in |- *.
  red in |- *; intros; discriminate.
  intros q'; rewrite (fun x y => plus_comm x (S y)); simpl in |- *; red in |- *;
    intros; discriminate.
  intros p' H q; case q.
  simpl in |- *; red in |- *; intros; discriminate.
  intros q'; red in |- *; intros H0; case (H q').
  replace (2 * q') with (2 * S q' - 2).
  rewrite <- H0; simpl in |- *; auto.
  repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *; auto.
  simpl in |- *; repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *;
    auto.
  case q'; simpl in |- *; auto.
Qed.


(** * Tail-recursive mult *)

(** [tail_mult] is an alternative definition for [mult] which is 
    tail-recursive, whereas [mult] is not. This can be useful 
    when extracting programs. *)

Fixpoint mult_acc (s:nat) m n {struct n} : nat :=
  match n with
    | O => s
    | S p => mult_acc (tail_plus m s) m p
  end.

Lemma mult_acc_aux : forall n m p, m + n * p = mult_acc m p n.
Proof.
  induction n as [| p IHp]; simpl in |- *; auto.
  intros s m; rewrite <- plus_tail_plus; rewrite <- IHp.
  rewrite <- plus_assoc_reverse; apply (f_equal2 (A1:=nat) (A2:=nat)); auto.
  rewrite plus_comm; auto.
Qed.

Definition tail_mult n m := mult_acc 0 m n.

Lemma mult_tail_mult : forall n m, n * m = tail_mult n m.
Proof.
  intros; unfold tail_mult in |- *; rewrite <- mult_acc_aux; auto.
Qed.

(** [TailSimpl] transforms any [tail_plus] and [tail_mult] into [plus] 
    and [mult] and simplify *)

Ltac tail_simpl :=
  repeat rewrite <- plus_tail_plus; repeat rewrite <- mult_tail_mult;
    simpl in |- *.