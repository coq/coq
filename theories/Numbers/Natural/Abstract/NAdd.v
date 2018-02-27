(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export NBase.

Module NAddProp (Import N : NAxiomsMiniSig').
Include NBaseProp N.

(** For theorems about [add] that are both valid for [N] and [Z], see [NZAdd] *)
(** Now comes theorems valid for natural numbers but not for Z *)

Theorem eq_add_0 : forall n m, n + m == 0 <-> n == 0 /\ m == 0.
Proof.
intros n m; induct n.
nzsimpl; intuition.
intros n IH. nzsimpl.
setoid_replace (S (n + m) == 0) with False by
 (apply neg_false; apply neq_succ_0).
setoid_replace (S n == 0) with False by
 (apply neg_false; apply neq_succ_0). tauto.
Qed.

Theorem eq_add_succ :
  forall n m, (exists p, n + m == S p) <->
              (exists n', n == S n') \/ (exists m', m == S m').
Proof.
intros n m; cases n.
split; intro H.
destruct H as [p H]. rewrite add_0_l in H; right; now exists p.
destruct H as [[n' H] | [m' H]].
symmetry in H; false_hyp H neq_succ_0.
exists m'; now rewrite add_0_l.
intro n; split; intro H.
left; now exists n.
exists (n + m); now rewrite add_succ_l.
Qed.

Theorem eq_add_1 : forall n m,
  n + m == 1 -> n == 1 /\ m == 0 \/ n == 0 /\ m == 1.
Proof.
intros n m. rewrite one_succ. intro H.
assert (H1 : exists p, n + m == S p) by now exists 0.
apply eq_add_succ in H1. destruct H1 as [[n' H1] | [m' H1]].
left. rewrite H1 in H; rewrite add_succ_l in H; apply succ_inj in H.
apply eq_add_0 in H. destruct H as [H2 H3]; rewrite H2 in H1; now split.
right. rewrite H1 in H; rewrite add_succ_r in H; apply succ_inj in H.
apply eq_add_0 in H. destruct H as [H2 H3]; rewrite H3 in H1; now split.
Qed.

Theorem succ_add_discr : forall n m, m ~= S (n + m).
Proof.
intro n; induct m.
apply neq_sym. apply neq_succ_0.
intros m IH H. apply succ_inj in H. rewrite add_succ_r in H.
unfold not in IH; now apply IH.
Qed.

Theorem add_pred_l : forall n m, n ~= 0 -> P n + m == P (n + m).
Proof.
intros n m; cases n.
intro H; now elim H.
intros n IH; rewrite add_succ_l; now do 2 rewrite pred_succ.
Qed.

Theorem add_pred_r : forall n m, m ~= 0 -> n + P m == P (n + m).
Proof.
intros n m H; rewrite (add_comm n (P m));
rewrite (add_comm n m); now apply add_pred_l.
Qed.

End NAddProp.

