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

Require Export ZBase.

Module ZPlusPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZBasePropMod := ZBasePropFunct ZAxiomsMod.
Open Local Scope IntScope.

Theorem Zadd_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> n1 + m1 == n2 + m2.
Proof NZadd_wd.

Theorem Zadd_0_l : forall n : Z, 0 + n == n.
Proof NZadd_0_l.

Theorem Zadd_succ_l : forall n m : Z, (S n) + m == S (n + m).
Proof NZadd_succ_l.

Theorem Zminus_0_r : forall n : Z, n - 0 == n.
Proof NZminus_0_r.

Theorem Zminus_succ_r : forall n m : Z, n - (S m) == P (n - m).
Proof NZminus_succ_r.

Theorem Zopp_0 : - 0 == 0.
Proof Zopp_0.

Theorem Zopp_succ : forall n : Z, - (S n) == P (- n).
Proof Zopp_succ.

(* Theorems that are valid for both natural numbers and integers *)

Theorem Zadd_0_r : forall n : Z, n + 0 == n.
Proof NZadd_0_r.

Theorem Zadd_succ_r : forall n m : Z, n + S m == S (n + m).
Proof NZadd_succ_r.

Theorem Zadd_comm : forall n m : Z, n + m == m + n.
Proof NZadd_comm.

Theorem Zadd_assoc : forall n m p : Z, n + (m + p) == (n + m) + p.
Proof NZadd_assoc.

Theorem Zadd_shuffle1 : forall n m p q : Z, (n + m) + (p + q) == (n + p) + (m + q).
Proof NZadd_shuffle1.

Theorem Zadd_shuffle2 : forall n m p q : Z, (n + m) + (p + q) == (n + q) + (m + p).
Proof NZadd_shuffle2.

Theorem Zadd_1_l : forall n : Z, 1 + n == S n.
Proof NZadd_1_l.

Theorem Zadd_1_r : forall n : Z, n + 1 == S n.
Proof NZadd_1_r.

Theorem Zadd_cancel_l : forall n m p : Z, p + n == p + m <-> n == m.
Proof NZadd_cancel_l.

Theorem Zadd_cancel_r : forall n m p : Z, n + p == m + p <-> n == m.
Proof NZadd_cancel_r.

(* Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zadd_pred_l : forall n m : Z, P n + m == P (n + m).
Proof.
intros n m.
rewrite <- (Zsucc_pred n) at 2.
rewrite Zadd_succ_l. now rewrite Zpred_succ.
Qed.

Theorem Zadd_pred_r : forall n m : Z, n + P m == P (n + m).
Proof.
intros n m; rewrite (Zadd_comm n (P m)), (Zadd_comm n m);
apply Zadd_pred_l.
Qed.

Theorem Zadd_opp_r : forall n m : Z, n + (- m) == n - m.
Proof.
NZinduct m.
rewrite Zopp_0; rewrite Zminus_0_r; now rewrite Zadd_0_r.
intro m. rewrite Zopp_succ, Zminus_succ_r, Zadd_pred_r; now rewrite Zpred_inj_wd.
Qed.

Theorem Zminus_0_l : forall n : Z, 0 - n == - n.
Proof.
intro n; rewrite <- Zadd_opp_r; now rewrite Zadd_0_l.
Qed.

Theorem Zminus_succ_l : forall n m : Z, S n - m == S (n - m).
Proof.
intros n m; do 2 rewrite <- Zadd_opp_r; now rewrite Zadd_succ_l.
Qed.

Theorem Zminus_pred_l : forall n m : Z, P n - m == P (n - m).
Proof.
intros n m. rewrite <- (Zsucc_pred n) at 2.
rewrite Zminus_succ_l; now rewrite Zpred_succ.
Qed.

Theorem Zminus_pred_r : forall n m : Z, n - (P m) == S (n - m).
Proof.
intros n m. rewrite <- (Zsucc_pred m) at 2.
rewrite Zminus_succ_r; now rewrite Zsucc_pred.
Qed.

Theorem Zopp_pred : forall n : Z, - (P n) == S (- n).
Proof.
intro n. rewrite <- (Zsucc_pred n) at 2.
rewrite Zopp_succ. now rewrite Zsucc_pred.
Qed.

Theorem Zminus_diag : forall n : Z, n - n == 0.
Proof.
NZinduct n.
now rewrite Zminus_0_r.
intro n. rewrite Zminus_succ_r, Zminus_succ_l; now rewrite Zpred_succ.
Qed.

Theorem Zadd_opp_diag_l : forall n : Z, - n + n == 0.
Proof.
intro n; now rewrite Zadd_comm, Zadd_opp_r, Zminus_diag.
Qed.

Theorem Zadd_opp_diag_r : forall n : Z, n + (- n) == 0.
Proof.
intro n; rewrite Zadd_comm; apply Zadd_opp_diag_l.
Qed.

Theorem Zadd_opp_l : forall n m : Z, - m + n == n - m.
Proof.
intros n m; rewrite <- Zadd_opp_r; now rewrite Zadd_comm.
Qed.

Theorem Zadd_minus_assoc : forall n m p : Z, n + (m - p) == (n + m) - p.
Proof.
intros n m p; do 2 rewrite <- Zadd_opp_r; now rewrite Zadd_assoc.
Qed.

Theorem Zopp_involutive : forall n : Z, - (- n) == n.
Proof.
NZinduct n.
now do 2 rewrite Zopp_0.
intro n. rewrite Zopp_succ, Zopp_pred; now rewrite Zsucc_inj_wd.
Qed.

Theorem Zopp_add_distr : forall n m : Z, - (n + m) == - n + (- m).
Proof.
intros n m; NZinduct n.
rewrite Zopp_0; now do 2 rewrite Zadd_0_l.
intro n. rewrite Zadd_succ_l; do 2 rewrite Zopp_succ; rewrite Zadd_pred_l.
now rewrite Zpred_inj_wd.
Qed.

Theorem Zopp_minus_distr : forall n m : Z, - (n - m) == - n + m.
Proof.
intros n m; rewrite <- Zadd_opp_r, Zopp_add_distr.
now rewrite Zopp_involutive.
Qed.

Theorem Zopp_inj : forall n m : Z, - n == - m -> n == m.
Proof.
intros n m H. apply Zopp_wd in H. now do 2 rewrite Zopp_involutive in H.
Qed.

Theorem Zopp_inj_wd : forall n m : Z, - n == - m <-> n == m.
Proof.
intros n m; split; [apply Zopp_inj | apply Zopp_wd].
Qed.

Theorem Zeq_opp_l : forall n m : Z, - n == m <-> n == - m.
Proof.
intros n m. now rewrite <- (Zopp_inj_wd (- n) m), Zopp_involutive.
Qed.

Theorem Zeq_opp_r : forall n m : Z, n == - m <-> - n == m.
Proof.
symmetry; apply Zeq_opp_l.
Qed.

Theorem Zminus_add_distr : forall n m p : Z, n - (m + p) == (n - m) - p.
Proof.
intros n m p; rewrite <- Zadd_opp_r, Zopp_add_distr, Zadd_assoc.
now do 2 rewrite Zadd_opp_r.
Qed.

Theorem Zminus_minus_distr : forall n m p : Z, n - (m - p) == (n - m) + p.
Proof.
intros n m p; rewrite <- Zadd_opp_r, Zopp_minus_distr, Zadd_assoc.
now rewrite Zadd_opp_r.
Qed.

Theorem minus_opp_l : forall n m : Z, - n - m == - m - n.
Proof.
intros n m. do 2 rewrite <- Zadd_opp_r. now rewrite Zadd_comm.
Qed.

Theorem Zminus_opp_r : forall n m : Z, n - (- m) == n + m.
Proof.
intros n m; rewrite <- Zadd_opp_r; now rewrite Zopp_involutive.
Qed.

Theorem Zadd_minus_swap : forall n m p : Z, n + m - p == n - p + m.
Proof.
intros n m p. rewrite <- Zadd_minus_assoc, <- (Zadd_opp_r n p), <- Zadd_assoc.
now rewrite Zadd_opp_l.
Qed.

Theorem Zminus_cancel_l : forall n m p : Z, n - m == n - p <-> m == p.
Proof.
intros n m p. rewrite <- (Zadd_cancel_l (n - m) (n - p) (- n)).
do 2 rewrite Zadd_minus_assoc. rewrite Zadd_opp_diag_l; do 2 rewrite Zminus_0_l.
apply Zopp_inj_wd.
Qed.

Theorem Zminus_cancel_r : forall n m p : Z, n - p == m - p <-> n == m.
Proof.
intros n m p.
stepl (n - p + p == m - p + p) by apply Zadd_cancel_r.
now do 2 rewrite <- Zminus_minus_distr, Zminus_diag, Zminus_0_r.
Qed.

(* The next several theorems are devoted to moving terms from one side of
an equation to the other. The name contains the operation in the original
equation (add or minus) and the indication whether the left or right term
is moved. *)

Theorem Zadd_move_l : forall n m p : Z, n + m == p <-> m == p - n.
Proof.
intros n m p.
stepl (n + m - n == p - n) by apply Zminus_cancel_r.
now rewrite Zadd_comm, <- Zadd_minus_assoc, Zminus_diag, Zadd_0_r.
Qed.

Theorem Zadd_move_r : forall n m p : Z, n + m == p <-> n == p - m.
Proof.
intros n m p; rewrite Zadd_comm; now apply Zadd_move_l.
Qed.

(* The two theorems above do not allow rewriting subformulas of the form
n - m == p to n == p + m since subtraction is in the right-hand side of
the equation. Hence the following two theorems. *)

Theorem Zminus_move_l : forall n m p : Z, n - m == p <-> - m == p - n.
Proof.
intros n m p; rewrite <- (Zadd_opp_r n m); apply Zadd_move_l.
Qed.

Theorem Zminus_move_r : forall n m p : Z, n - m == p <-> n == p + m.
Proof.
intros n m p; rewrite <- (Zadd_opp_r n m). now rewrite Zadd_move_r, Zminus_opp_r.
Qed.

Theorem Zadd_move_0_l : forall n m : Z, n + m == 0 <-> m == - n.
Proof.
intros n m; now rewrite Zadd_move_l, Zminus_0_l.
Qed.

Theorem Zadd_move_0_r : forall n m : Z, n + m == 0 <-> n == - m.
Proof.
intros n m; now rewrite Zadd_move_r, Zminus_0_l.
Qed.

Theorem Zminus_move_0_l : forall n m : Z, n - m == 0 <-> - m == - n.
Proof.
intros n m. now rewrite Zminus_move_l, Zminus_0_l.
Qed.

Theorem Zminus_move_0_r : forall n m : Z, n - m == 0 <-> n == m.
Proof.
intros n m. now rewrite Zminus_move_r, Zadd_0_l.
Qed.

(* The following section is devoted to cancellation of like terms. The name
includes the first operator and the position of the term being canceled. *)

Theorem Zadd_simpl_l : forall n m : Z, n + m - n == m.
Proof.
intros; now rewrite Zadd_minus_swap, Zminus_diag, Zadd_0_l.
Qed.

Theorem Zadd_simpl_r : forall n m : Z, n + m - m == n.
Proof.
intros; now rewrite <- Zadd_minus_assoc, Zminus_diag, Zadd_0_r.
Qed.

Theorem Zminus_simpl_l : forall n m : Z, - n - m + n == - m.
Proof.
intros; now rewrite <- Zadd_minus_swap, Zadd_opp_diag_l, Zminus_0_l.
Qed.

Theorem Zminus_simpl_r : forall n m : Z, n - m + m == n.
Proof.
intros; now rewrite <- Zminus_minus_distr, Zminus_diag, Zminus_0_r.
Qed.

(* Now we have two sums or differences; the name includes the two operators
and the position of the terms being canceled *)

Theorem Zadd_add_simpl_l_l : forall n m p : Z, (n + m) - (n + p) == m - p.
Proof.
intros n m p. now rewrite (Zadd_comm n m), <- Zadd_minus_assoc,
Zminus_add_distr, Zminus_diag, Zminus_0_l, Zadd_opp_r.
Qed.

Theorem Zadd_add_simpl_l_r : forall n m p : Z, (n + m) - (p + n) == m - p.
Proof.
intros n m p. rewrite (Zadd_comm p n); apply Zadd_add_simpl_l_l.
Qed.

Theorem Zadd_add_simpl_r_l : forall n m p : Z, (n + m) - (m + p) == n - p.
Proof.
intros n m p. rewrite (Zadd_comm n m); apply Zadd_add_simpl_l_l.
Qed.

Theorem Zadd_add_simpl_r_r : forall n m p : Z, (n + m) - (p + m) == n - p.
Proof.
intros n m p. rewrite (Zadd_comm p m); apply Zadd_add_simpl_r_l.
Qed.

Theorem Zminus_add_simpl_r_l : forall n m p : Z, (n - m) + (m + p) == n + p.
Proof.
intros n m p. now rewrite <- Zminus_minus_distr, Zminus_add_distr, Zminus_diag,
Zminus_0_l, Zminus_opp_r.
Qed.

Theorem Zminus_add_simpl_r_r : forall n m p : Z, (n - m) + (p + m) == n + p.
Proof.
intros n m p. rewrite (Zadd_comm p m); apply Zminus_add_simpl_r_l.
Qed.

(* Of course, there are many other variants *)

End ZPlusPropFunct.

