(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

Section Sigma.

Require Rbase.

Variable f : nat->R.

Fixpoint sigma_aux [low, high: nat;diff : nat] : R :=
Cases diff of
O  => (f low)
| (S p) => (Rplus (f low) (sigma_aux (S low) high p)) 
end.

Parameter sigma : nat->nat->R.
Hypothesis  def_sigma : (low,high:nat) (le low high) -> (sigma low high)==(sigma_aux low high (minus high low)).

Lemma sigma_aux_inv : (diff,low,high,high2:nat) (sigma_aux low high diff)==(sigma_aux low high2 diff).
Unfold sigma_aux; Induction diff; [Intros; Reflexivity | Intros; Rewrite (H (S low) high high2); Reflexivity].
Qed.

Theorem sigma_split : (low,high,k:nat) (le low k)->(lt k high)->``(sigma low high)==(sigma low k)+(sigma (S k) high)``.
Intros.
Repeat Rewrite def_sigma.
Cut (d,e,n:nat) ((Rplus (sigma_aux n n d) (sigma_aux (plus n (S d)) (plus n (S d)) e))==(sigma_aux n n (plus d (S e)))).
Intros; Rewrite (sigma_aux_inv (minus high low) low high low); Rewrite (sigma_aux_inv (minus k low) low k low); Rewrite (sigma_aux_inv (minus high (S k)) (S k) high (S k)); Symmetry.
Cut (plus low (S (minus k low)))=(S k).
Cut (plus (minus k low) (S (minus high (S k))))=(minus high low).
Intros; Rewrite <- H2; Repeat Rewrite <- H3; Apply (H1 (minus k low) (minus high (plus low (S (minus k low))))).
Apply INR_eq; Repeat Rewrite plus_INR Orelse Rewrite minus_INR Orelse Rewrite S_INR; Try Ring.
Apply lt_le_S; Assumption.
Apply lt_le_weak; Apply le_lt_trans with k; Assumption.
Assumption.
Apply INR_eq; Repeat Rewrite plus_INR Orelse Rewrite minus_INR Orelse Rewrite S_INR; Try Ring.
Assumption.
Induction d.
Intros; Cut (plus n (S O))=(S n).
Cut (plus O (S e))=(S e).
Intros; Repeat Rewrite H2; Rewrite H1; Rewrite (sigma_aux_inv (S e) n n (S n)); Unfold sigma_aux; Reflexivity.
Auto.
Apply INR_eq; Repeat Rewrite plus_INR Orelse Rewrite S_INR; Try Ring.
Intros; Cut (plus (S n) (S e))=(S (plus n (S e))).
Intro; Rewrite H2; Unfold sigma_aux; Fold sigma_aux; Cut (plus n0 (S (S n)))=(plus (S n0) (S n)).
Intro; Repeat Rewrite H3; Rewrite (sigma_aux_inv n (S n0) n0 (S n0)); Rewrite Rplus_assoc; Rewrite (H1 e (S n0)); Rewrite (sigma_aux_inv (plus n (S e)) (S n0) n0 (S n0)); Reflexivity.
Apply INR_eq; Repeat Rewrite plus_INR Orelse Rewrite S_INR; Try Ring.
Apply INR_eq; Repeat Rewrite plus_INR Orelse Rewrite S_INR; Try Ring.
Apply lt_le_S; Assumption.
Assumption.
Apply lt_le_weak; Apply le_lt_trans with k; Assumption.
Qed.

Theorem sigma_diff : (low,high,k:nat) (le low k) -> (lt k high )->``(sigma low high)-(sigma low k)==(sigma (S k) high)``.
Intros low high k H1 H2; Symmetry; Rewrite -> (sigma_split H1 H2); Ring.
Qed.

Theorem sigma_diff_neg : (low,high,k:nat) (le low k) -> (lt k high)-> ``(sigma low k)-(sigma low high)==-(sigma (S k) high)``.
Intros low high k H1 H2; Rewrite -> (sigma_split H1 H2); Ring.
Qed.

Theorem sigma_first : (low,high:nat) (lt low high) -> ``(sigma low high)==(f low)+(sigma (S low) high)``.
Intros low high H1; Generalize (lt_le_S low high H1); Intro H2; Generalize (lt_le_weak low high H1); Intro H3; Replace ``(f low)`` with ``(sigma low low)``; [Apply sigma_split; Trivial | Rewrite def_sigma; [Replace (minus low low) with O; Ring; Apply minus_n_n | Trivial]].
Qed.

Theorem sigma_last : (low,high:nat) (lt low high) -> ``(sigma low high)==(f high)+(sigma low (pred high))``.
Intros low high H1; Generalize (lt_le_S low high H1); Intro H2; Generalize (lt_le_weak low high H1); Intro H3; Replace ``(f high)`` with ``(sigma high high)``; [Rewrite Rplus_sym; Pattern 3 high; Rewrite (S_pred high low H1); Apply sigma_split; [Apply gt_S_le; Rewrite <- (S_pred high low H1); Assumption | Pattern 2 high; Rewrite (S_pred high low H1); Apply lt_n_Sn] | Rewrite def_sigma; [ Rewrite <- (minus_n_n high) | Trivial ]; Trivial].
Qed.

Theorem sigma_eq_arg : (low:nat) (sigma low low)==(f low).
Intro low; Rewrite def_sigma; [Rewrite <- (minus_n_n low); Trivial | Trivial].
Qed.

End Sigma.
