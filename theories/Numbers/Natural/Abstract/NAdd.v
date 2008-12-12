(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NBase.

Module NAddPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NBasePropMod := NBasePropFunct NAxiomsMod.

Open Local Scope NatScope.

Theorem add_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> n1 + m1 == n2 + m2.
Proof NZadd_wd.

Theorem add_0_l : forall n : N, 0 + n == n.
Proof NZadd_0_l.

Theorem add_succ_l : forall n m : N, (S n) + m == S (n + m).
Proof NZadd_succ_l.

(** Theorems that are valid for both natural numbers and integers *)

Theorem add_0_r : forall n : N, n + 0 == n.
Proof NZadd_0_r.

Theorem add_succ_r : forall n m : N, n + S m == S (n + m).
Proof NZadd_succ_r.

Theorem add_comm : forall n m : N, n + m == m + n.
Proof NZadd_comm.

Theorem add_assoc : forall n m p : N, n + (m + p) == (n + m) + p.
Proof NZadd_assoc.

Theorem add_shuffle1 : forall n m p q : N, (n + m) + (p + q) == (n + p) + (m + q).
Proof NZadd_shuffle1.

Theorem add_shuffle2 : forall n m p q : N, (n + m) + (p + q) == (n + q) + (m + p).
Proof NZadd_shuffle2.

Theorem add_1_l : forall n : N, 1 + n == S n.
Proof NZadd_1_l.

Theorem add_1_r : forall n : N, n + 1 == S n.
Proof NZadd_1_r.

Theorem add_cancel_l : forall n m p : N, p + n == p + m <-> n == m.
Proof NZadd_cancel_l.

Theorem add_cancel_r : forall n m p : N, n + p == m + p <-> n == m.
Proof NZadd_cancel_r.

(* Theorems that are valid for natural numbers but cannot be proved for Z *)

Theorem eq_add_0 : forall n m : N, n + m == 0 <-> n == 0 /\ m == 0.
Proof.
intros n m; induct n.
(* The next command does not work with the axiom add_0_l from NAddSig *)
rewrite add_0_l. intuition reflexivity.
intros n IH. rewrite add_succ_l.
setoid_replace (S (n + m) == 0) with False using relation iff by
 (apply -> neg_false; apply neq_succ_0).
setoid_replace (S n == 0) with False using relation iff by
 (apply -> neg_false; apply neq_succ_0). tauto.
Qed.

Theorem eq_add_succ :
  forall n m : N, (exists p : N, n + m == S p) <->
                    (exists n' : N, n == S n') \/ (exists m' : N, m == S m').
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

Theorem eq_add_1 : forall n m : N,
  n + m == 1 -> n == 1 /\ m == 0 \/ n == 0 /\ m == 1.
Proof.
intros n m H.
assert (H1 : exists p : N, n + m == S p) by now exists 0.
apply -> eq_add_succ in H1. destruct H1 as [[n' H1] | [m' H1]].
left. rewrite H1 in H; rewrite add_succ_l in H; apply succ_inj in H.
apply -> eq_add_0 in H. destruct H as [H2 H3]; rewrite H2 in H1; now split.
right. rewrite H1 in H; rewrite add_succ_r in H; apply succ_inj in H.
apply -> eq_add_0 in H. destruct H as [H2 H3]; rewrite H3 in H1; now split.
Qed.

Theorem succ_add_discr : forall n m : N, m ~= S (n + m).
Proof.
intro n; induct m.
apply neq_sym. apply neq_succ_0.
intros m IH H. apply succ_inj in H. rewrite add_succ_r in H.
unfold not in IH; now apply IH.
Qed.

Theorem add_pred_l : forall n m : N, n ~= 0 -> P n + m == P (n + m).
Proof.
intros n m; cases n.
intro H; now elim H.
intros n IH; rewrite add_succ_l; now do 2 rewrite pred_succ.
Qed.

Theorem add_pred_r : forall n m : N, m ~= 0 -> n + P m == P (n + m).
Proof.
intros n m H; rewrite (add_comm n (P m));
rewrite (add_comm n m); now apply add_pred_l.
Qed.

(* One could define n <= m as exists p : N, p + n == m. Then we have
dichotomy:

forall n m : N, n <= m \/ m <= n,

i.e.,

forall n m : N, (exists p : N, p + n == m) \/ (exists p : N, p + m == n)     (1)

We will need (1) in the proof of induction principle for integers
constructed as pairs of natural numbers. The formula (1) can be proved
using properties of order and truncated subtraction. Thus, p would be
m - n or n - m and (1) would hold by theorem sub_add from Sub.v
depending on whether n <= m or m <= n. However, in proving induction
for integers constructed from natural numbers we do not need to
require implementations of order and sub; it is enough to prove (1)
here. *)

Theorem add_dichotomy :
  forall n m : N, (exists p : N, p + n == m) \/ (exists p : N, p + m == n).
Proof.
intros n m; induct n.
left; exists m; apply add_0_r.
intros n IH.
destruct IH as [[p H] | [p H]].
destruct (zero_or_succ p) as [H1 | [p' H1]]; rewrite H1 in H.
rewrite add_0_l in H. right; exists (S 0); rewrite H; rewrite add_succ_l; now rewrite add_0_l.
left; exists p'; rewrite add_succ_r; now rewrite add_succ_l in H.
right; exists (S p). rewrite add_succ_l; now rewrite H.
Qed.

End NAddPropFunct.

