(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Rseries.
Require PartSum.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Set Implicit Arguments.

Section Sigma.

Variable f : nat->R.

Definition sigma [low,high:nat] : R := (sum_f_R0 [k:nat](f (plus low k)) (minus high low)).

Theorem sigma_split : (low,high,k:nat) (le low k)->(lt k high)->``(sigma low high)==(sigma low k)+(sigma (S k) high)``.
Intros; Induction k.
Cut low = O.
Intro; Rewrite H1; Unfold sigma; Rewrite <- minus_n_n; Rewrite <- minus_n_O; Simpl; Replace (minus high (S O)) with (pred high).
Apply (decomp_sum [k:nat](f k)).
Assumption.
Apply pred_of_minus.
Inversion H; Reflexivity.
Cut (le low k)\/low=(S k).
Intro; Elim H1; Intro.
Replace (sigma low (S k)) with ``(sigma low k)+(f (S k))``.
Rewrite Rplus_assoc; Replace ``(f (S k))+(sigma (S (S k)) high)`` with (sigma (S k) high).
Apply Hreck.
Assumption.
Apply lt_trans with (S k); [Apply lt_n_Sn | Assumption].
Unfold sigma; Replace (minus high (S (S k))) with (pred (minus high (S k))).
Pattern 3 (S k); Replace (S k) with (plus (S k) O); [Idtac | Ring].
Replace (sum_f_R0 [k0:nat](f (plus (S (S k)) k0)) (pred (minus high (S k)))) with (sum_f_R0 [k0:nat](f (plus (S k) (S k0))) (pred (minus high (S k)))).
Apply (decomp_sum [i:nat](f (plus (S k) i))).
Apply lt_minus_O_lt; Assumption.
Apply sum_eq; Intros; Replace (plus (S k) (S i)) with (plus (S (S k)) i).
Reflexivity.
Apply INR_eq; Do 2 Rewrite plus_INR; Do 3 Rewrite S_INR; Ring.
Replace (minus high (S (S k))) with (minus (minus high (S k)) (S O)).
Apply pred_of_minus.
Apply INR_eq; Repeat  Rewrite minus_INR.
Do 4 Rewrite S_INR; Ring.
Apply lt_le_S; Assumption.
Apply lt_le_weak; Assumption.
Apply lt_le_S; Apply lt_minus_O_lt; Assumption.
Unfold sigma; Replace (minus (S k) low) with (S (minus k low)).
Pattern 1 (S k); Replace (S k) with (plus low (S (minus k low))).
Symmetry; Apply (tech5 [i:nat](f (plus low i))).
Apply INR_eq; Rewrite plus_INR; Do 2 Rewrite S_INR; Rewrite minus_INR.
Ring.
Assumption.
Apply minus_Sn_m; Assumption.
Rewrite <- H2; Unfold sigma; Rewrite <- minus_n_n; Simpl; Replace (minus high (S low)) with (pred (minus high low)).
Replace (sum_f_R0 [k0:nat](f (S (plus low k0))) (pred (minus high low))) with (sum_f_R0 [k0:nat](f (plus low (S k0))) (pred (minus high low))).
Apply (decomp_sum [k0:nat](f (plus low k0))).
Apply lt_minus_O_lt.
Apply le_lt_trans with (S k); [Rewrite H2; Apply le_n | Assumption].
Apply sum_eq; Intros; Replace (S (plus low i)) with (plus low (S i)).
Reflexivity.
Apply INR_eq; Rewrite plus_INR; Do 2 Rewrite S_INR; Rewrite plus_INR; Ring.
Replace (minus high (S low)) with (minus (minus high low) (S O)).
Apply pred_of_minus.
Apply INR_eq; Repeat  Rewrite minus_INR.
Do 2 Rewrite S_INR; Ring.
Apply lt_le_S; Rewrite H2; Assumption.
Rewrite H2; Apply lt_le_weak; Assumption.
Apply lt_le_S; Apply lt_minus_O_lt; Rewrite H2; Assumption.
Inversion H; [
  Right; Reflexivity
| Left; Assumption].
Qed.

Theorem sigma_diff : (low,high,k:nat) (le low k) -> (lt k high )->``(sigma low high)-(sigma low k)==(sigma (S k) high)``.
Intros low high k H1 H2; Symmetry; Rewrite -> (sigma_split H1 H2); Ring.
Qed.

Theorem sigma_diff_neg : (low,high,k:nat) (le low k) -> (lt k high)-> ``(sigma low k)-(sigma low high)==-(sigma (S k) high)``.
Intros low high k H1 H2; Rewrite -> (sigma_split H1 H2); Ring.
Qed.

Theorem sigma_first : (low,high:nat) (lt low high) -> ``(sigma low high)==(f low)+(sigma (S low) high)``.
Intros low high H1; Generalize (lt_le_S low high H1); Intro H2; Generalize (lt_le_weak low high H1); Intro H3; Replace ``(f low)`` with ``(sigma low low)``.
Apply sigma_split.
Apply le_n.
Assumption.
Unfold sigma; Rewrite <- minus_n_n.
Simpl.
Replace (plus low O) with low; [Reflexivity | Ring].
Qed.

Theorem sigma_last : (low,high:nat) (lt low high) -> ``(sigma low high)==(f high)+(sigma low (pred high))``.
Intros low high H1; Generalize (lt_le_S low high H1); Intro H2; Generalize (lt_le_weak low high H1); Intro H3; Replace ``(f high)`` with ``(sigma high high)``.
Rewrite Rplus_sym; Cut high = (S (pred high)).
Intro; Pattern 3 high; Rewrite H.
Apply sigma_split.
Apply le_S_n; Rewrite <- H; Apply lt_le_S; Assumption.
Apply lt_pred_n_n; Apply le_lt_trans with low; [Apply le_O_n | Assumption].
Apply S_pred with O; Apply le_lt_trans with low; [Apply le_O_n | Assumption].
Unfold sigma; Rewrite <- minus_n_n; Simpl; Replace (plus high O) with high; [Reflexivity | Ring].
Qed.

Theorem sigma_eq_arg : (low:nat) (sigma low low)==(f low).
Intro; Unfold sigma; Rewrite <- minus_n_n.
Simpl; Replace (plus low O) with low; [Reflexivity | Ring].
Qed.

End Sigma.
