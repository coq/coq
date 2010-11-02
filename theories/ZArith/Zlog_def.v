(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Zorder Zpow_def.

Local Open Scope Z_scope.

(** Definition of Zlog2 *)

(** TODO: this is equal to Zlogarithm.log_inf *)

Fixpoint Plog2_Z (p:positive) : Z :=
  match p with
    | 1 => Z0
    | p~0 => Zsucc (Plog2_Z p)
    | p~1 => Zsucc (Plog2_Z p)
  end%positive.

Definition Zlog2 z :=
  match z with
    | Zpos p => Plog2_Z p
    | _ => 0
  end.

Lemma Plog2_Z_nonneg : forall p, 0 <= Plog2_Z p.
Proof.
 induction p; simpl; auto with zarith.
Qed.

(** TODO : to move ... *)

Lemma Zle_succ_l : forall n m, Zsucc n <= m <-> n < m.
Proof.
 intros. split; intros H.
 rewrite (Zsucc_pred m). apply Zle_lt_succ, Zsucc_le_reg.
 now rewrite <- Zsucc_pred.
 now apply Zlt_le_succ.
Qed.

Lemma Plog2_Z_spec : forall p,
 2^(Plog2_Z p) <= Zpos p < 2^(Zsucc (Plog2_Z p)).
Proof.
 induction p; simpl;
  try rewrite 2 Zpower_succ_r; auto using Plog2_Z_nonneg with zarith.
 (* p~1 *)
 change (Zpos p~1) with (Zsucc (2 * Zpos p)).
 split; destruct IHp as [LE LT].
 apply Zle_trans with (2 * Zpos p).
 now apply Zmult_le_compat_l.
 apply Zle_succ.
 apply Zle_succ_l. apply Zle_succ_l in LT.
 replace (Zsucc (Zsucc (2 * Zpos p))) with (2 * (Zsucc (Zpos p))).
 now apply Zmult_le_compat_l.
 simpl. now rewrite Pplus_one_succ_r.
 (* p~0 *)
 change (Zpos p~0) with (2 * Zpos p).
 split; destruct IHp.
 now apply Zmult_le_compat_l.
 now apply Zmult_lt_compat_l.
 (* 1 *)
 now split.
Qed.

Lemma Zlog2_spec : forall n, 0 < n ->
 2^(Zlog2 n) <= n < 2^(Zsucc (Zlog2 n)).
Proof.
 intros [|p|p] Hn; try discriminate. apply Plog2_Z_spec.
Qed.

Lemma Zlog2_nonpos : forall n, n<=0 -> Zlog2 n = 0.
Proof.
 intros [|p|p] Hn. reflexivity. now destruct Hn. reflexivity.
Qed.
